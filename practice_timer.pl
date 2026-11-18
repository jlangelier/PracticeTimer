#!/usr/bin/env perl
use strict;
use warnings;
use Time::HiRes qw(time sleep);
use Term::ReadKey;
use POSIX qw(strftime);
use Time::Local qw(timelocal timegm);
use File::Spec;
use File::Copy qw(copy);
use FindBin qw($Bin);
use lib $Bin;
use PracticeTips ();
use PracticeQuotes qw(next_quote);
use PracticeKeys qw(initialize poll_key);
use PracticeAudit qw(append_events);

$| = 1;

# The main status and selected-song timers refresh once a second; category
# timers and practice-day rankings continue refreshing every ten seconds.
my $STATUS_LINE_UPDATE_INTERVAL = 1;
my $UPDATE_INTERVAL = 10;

# In-memory main-screen cache.  Screen refreshes compare physical console rows
# and update only those that changed. Menus/alerts invalidate the cache.
my @main_screen_last_lines;
my $main_screen_cache_valid = 0;
my $main_screen_last_geometry = '';
# Position of the status line in the visible, possibly clipped physical frame.
# A long status line may occupy more than one console row.
my $main_screen_status_first_row = -1;
my $main_screen_status_row_count = 0;
# Song/session clocks have their own physical row locations; these can vary
# if the status line or the current-song title wraps in a narrow console.
my $main_screen_song_first_row = -1;
my $main_screen_song_row_count = 0;
my $main_screen_pending_first_row = -1;
my $main_screen_pending_row_count = 0;
my $main_screen_song_line_present = 0;
my $main_screen_pending_line_present = 0;
my $main_screen_cached_percentiles = '';
my $win_console_output;
my $win_console_output_checked = 0;


# Once per idle stretch, interrupt the main screen after ten minutes without
# actively timed practice, hold the alert for five seconds, then redraw.
my $IDLE_ALERT_AFTER_SECONDS = 10 * 60;
my $IDLE_ALERT_HOLD_SECONDS  = 5;

# Advance to the next quote on each launch, with history stored in quotes.txt.
my $QUOTES_FILE = File::Spec->catfile($Bin, 'quotes.txt');
my $CURRENT_QUOTE = '';

# Minimum actual practice (excluding Pause) required before a timer session
# enters the historical TSV logs. The reloadable session state is ALWAYS saved.
# Scales and Ear training count as practice outside target percentages.
my $MIN_LOGGED_PRACTICE_SECONDS = 60;

# Each individual song selection needs 60 seconds of actual playing before
# its time and selection count enter the per-song totals. Category time is
# still counted normally. Menu time, pausing and changing songs cannot be
# combined to turn several accidental selections into a qualifying one.
my $MIN_SONG_SELECTION_SECONDS = 60;

# Category percentages are based on active practice time only.
# Change this to 1 if you want Pause time included in the category percentage denominator.
my $COUNT_PAUSE_IN_PERCENT = 0;

# Scales and Ear training are measured against ALL active practice, including
# repertoire, Theory, Scales and Ear training (never Pause). Unlike the song
# categories, these percentages do not share the repertoire denominator.
my $SUPPLEMENTAL_TARGET_MIN_PERCENT = 5;
my $SUPPLEMENTAL_TARGET_MAX_PERCENT = 20;
# Scales are HIGH after 30 minutes of this session's total Scales time,
# regardless of the percentage. Exactly 30 minutes is still permitted.
my $SCALES_HIGH_AFTER_SECONDS = 30 * 60;
# Theory is a daily minutes target, not a percentage of repertoire time.
my $THEORY_DAILY_MIN_SECONDS = 10 * 60;
my $THEORY_DAILY_MAX_SECONDS = 20 * 60;

# Machine-readable saved session. This is overwritten on save/quit and is used for reload.
my $STATE_FILE = 'practice_timer_session.state';

# Last instant actual practice was timed, independent of /n and /r.
# Stored separately so a new practice day does not reset the idle clock.
my $LAST_PRACTICE_FILE = 'practice_last_active.state';
my $last_practice_epoch = 0;
my $last_practice_written_epoch = 0;
# The practice timestamp for which the idle alert was already shown.
# This survives /r and restarts so an overdue pause does not alert repeatedly.
my $last_idle_alert_for_epoch = 0;

# Human-readable historical log. This is appended to on save/quit.
my $LOG_FILE = 'practice_time_log.tsv';

# Per-song cumulative snapshots. The fourth column (song_id) of
# practice_song_categories.tsv is the permanent identity of a song.
# Each save writes the cumulative time for the current session; the report
# uses the last snapshot for each (session_start, song_id) pair.
my $SONG_LOG_FILE = 'practice_song_time_log.tsv';

# Append-only dated corrections for practice done when the timer was not running.
# Positive and negative entries are preserved as an audit trail. These entries
# are separate from the session snapshots and are never counted twice on save.
my $SONG_ADJUST_FILE = 'practice_song_adjustments.tsv';

# Summary report generated from the TSV log before the program exits.
my $REPORT_FILE = 'practice_activity_report.txt';

# Statistics and history reports begin on this practice date, inclusive.
# Change to another YYYY-MM-DD date, or use '' for all recorded history.
# The cutoff affects calculations only: older logs and state are never altered.
# Calendar, streak, and daily rankings count practice on the actual local day.
my $STATISTICS_START_DATE = '2026-11-03';

sub statistics_include_date {
    my ($stamp_or_date) = @_;
    return 1 if $STATISTICS_START_DATE eq '';
    return 0 unless defined($stamp_or_date)
        && $stamp_or_date =~ /\A(\d{4}-\d{2}-\d{2})(?:\s|\z)/;
    return $1 ge $STATISTICS_START_DATE ? 1 : 0;
}

# Song list grouped by practice category.
# TSV columns: level, number, song title, song_id, [archived].
# Archived songs retain their permanent IDs and all linked history/media.
# The fifth column is optional; normal/legacy rows still use four columns.
# Empty lines are ignored. Lines whose first non-space character is #
# are comments (not song rows). Comments are preserved when the TSV is
# rewritten: opening/trailing comments stay at the ends of the catalog, and
# comments between songs travel with the song immediately following them.
# Valid song levels are 0 through 6.
my $SONG_CATEGORY_FILE = 'practice_song_categories.tsv';

# Header/footer comments cannot be attached to an individual song. Keep them
# per file for the read -> edit -> write operations performed by the song menu.
my %song_category_comment_layout;

# Optional song attributes, keyed by permanent song_id, one attribute per row.
# A separate file keeps category numbers, titles, media and history untouched.
my $SONG_ATTRIBUTES_FILE = 'practice_song_attributes.tsv';
my $MEMORIZED_REPORT_FILE = 'practice_memorized_songs_report.txt';
my $EMPHASIZE_REPORT_FILE = 'practice_emphasized_songs_report.txt';

# Until we track independent pass/fail memory tests, prompt the user to
# check memorized songs after this many days WITHOUT credited song practice.
# Adjust this number to change how often memory checks become due.
my $MEMORIZED_REVIEW_INTERVAL_DAYS = 14;

# Append-only record of deliberate repertoire and practice-data changes.
my $AUDIT_FILE = 'practice_audit_log.tsv';
my $audit_alert = '';

# Sheet music links/paths for songs.
# TSV columns: song_id, path_or_link.
# The path_or_link may be a Google Drive path, PDF, TXT, image, URL, or any
# arbitrary system file that you want treated as sheet music.
my $SHEET_MUSIC_FILE = 'practice_song_sheet_music.tsv';

# Unlimited MP3 attachments: one TSV row per (song_id, file path).
# Old one-row-per-song files still work. On selection, VLC starts playing
# the first MP3 and loads the rest into its playlist, in attachment order.
my $SONG_AUDIO_FILE = 'practice_song_audio.tsv';

# Folder used when attaching an MP3 by filename rather than by full path.
my $SONG_AUDIO_DIR = 'G:\My Drive\mp3';

# Zero or more TXT/PDF/ODT/JPG/PNG files per song, attached by permanent song ID.
my $SONG_TAB_FILE = 'practice_song_tabs.tsv';
my $SONG_TAB_DIR  = 'G:\My Drive\tab';

# Dedicated attachment handle for Scales. This is NOT a repertoire song and
# is never used for song totals or the 60-second song-selection minimum.
# The same existing TSV files store its attachments, keyed by this handle.
my $SCALES_ATTACHMENT_ID = '@scales';
# Ear training is another independently timed, non-song activity.
my $EAR_TRAINING_ATTACHMENT_ID = '@ear_training';
# Keep the old @jamming ID and j practice data untouched for historical use.
# The new Theory category has a DIFFERENT identity; old Jamming time must
# never be attributed to Theory.
my $JAMMING_ATTACHMENT_ID = '@jamming'; # retired; preserve existing TSV links
my $THEORY_ATTACHMENT_ID = '@theory';

# Optional explicit OpenOffice Writer executable. Leave blank for auto-detection.
# Example: 'C:\Program Files (x86)\OpenOffice 4\program\swriter.exe'
# Set this if OpenOffice is installed outside the usual Windows directories.
my $OPENOFFICE_WRITER_EXE = '';

# Optional full path to IrfanView (for JPG/JPEG/PNG attachments).
# Leave blank to search standard Windows installation folders and PATH.
# Examples: 'C:\Program Files\IrfanView\i_view64.exe' or
#           'C:\Program Files (x86)\IrfanView\i_view32.exe'
my $IRFANVIEW_EXE = '';

# Optional explicit Audacity executable. Leave blank to search the standard
# Windows install locations and PATH. For a portable or unusual installation,
# set the full path (for example, 'C:\Program Files\Audacity\Audacity.exe').
my $AUDACITY_EXE = '';

# Startup requires a command-line flag:
#
#   /n  Start a new session.
#   /r  Reload the saved session from $STATE_FILE.
#
# Optional manual session-start time for a NEW session:
#
#   YYYY-MM-DD HH:MM:SS
#
# Examples:
#   perl practice_timer.pl /n
#   perl practice_timer.pl /n "2026-06-16 09:28:48"
#   perl practice_timer.pl /r
#
# If no flag is supplied, usage is displayed and the script exits.
#
# While the timer is running, press:
#   s
# to track Scales practice. Press uppercase S to save immediately.
#
# Press y or number-row 9 to track Theory (10-20 minutes per day).
# Press c to view/edit the song category TSV grouped by level and number.
#
# Press uppercase T to manually reset the displayed session-start time.

my @options = (
    {
        key        => '0',
        name       => 'Keystones / Landmarks (1-2)',
        target_min => 0,
        target_max => 5,
        is_pause   => 0,
        is_adjust  => 0,
        desc       => 'Keystones are rare songs that have become part of your musical identity. They are not ordinary practice assignments and are not counted as daily workload. A Keystone may be revisited occasionally, but it does not need regular maintenance unless you deliberately revive it.',
    },
    {
        key        => '1',
        name       => 'Ready Core (5-10)',
        target_min => 20,
        target_max => 30,
        is_pause   => 0,
        is_adjust  => 0,
        desc       => 'Ready Core songs are songs you can play now and want to keep performance-ready.',
    },
    {
        key        => '2',
        name       => 'Active Development (5-8)',
        target_min => 30,
        target_max => 40,
        is_pause   => 0,
        is_adjust  => 0,
        desc       => 'Active Development is the main workshop. These are songs you can partly or mostly play, but which still need real work: transitions, timing, memory, tone, right-hand control, singing while playing, or problem sections.',
    },
    {
        key        => '3',
        name       => 'Incubator / Candidates (2-4)',
        target_min => 10,
        target_max => 20,
        is_pause   => 0,
        is_adjust  => 0,
        desc       => 'Incubator songs are new candidates being tested. They are not yet full commitments. A song in this category is being auditioned to see whether it deserves promotion to Active Development or should be dropped.',
    },
    {
        key        => '4',
        name       => 'Maintenance / Rotation (5-10)',
        target_min => 5,
        target_max => 15,
        is_pause   => 0,
        is_adjust  => 0,
        desc       => 'Maintenance songs are pieces you basically know but do not want to lose. You do not play all of them every day. You rotate through them lightly to keep the door unlocked.',
    },
    {
        key        => '5',
        name       => 'Back Burner',
        target_min => 0,
        target_max => 10,
        is_pause   => 0,
        is_adjust  => 0,
        desc       => 'Back Burner is for songs you want to keep in your repertoire without giving them regular priority. Practice them occasionally, whenever you feel like it. There is no minimum requirement; aim to spend no more than 10% of target-category practice here.',
    },
    {
        key        => '6',
        name       => 'Cold Storage',
        target_min => 0,
        target_max => 0,
        is_pause   => 0,
        is_adjust  => 0,
        desc       => 'Cold Storage songs are completed achievements: songs you have down and want to preserve as accomplishments, but which do not currently require scheduled practice time.',
    },
    {
        # Retained solely for parsing older practice logs and reloaded sessions.
        # Never select or display this category as a current practice option.
        key        => 'j',
        name       => 'Jamming (historical)',
        target_min => 0,
        target_max => 0,
        is_pause   => 0,
        is_adjust  => 0,
        is_retired => 1,
        desc       => 'Retired category. Old Jamming data is preserved; no new Jamming practice can be started.',
    },
    {
        key        => 'y',
        name       => 'Theory',
        target_min => 0,
        target_max => 0,
        is_pause   => 0,
        is_adjust  => 0,
        desc       => 'Music theory study, independently recorded with its own media attachments. Daily target: 10 to 20 minutes (LOW below 10, OK from 10 through 20, HIGH above 20). Theory is excluded from repertoire percentages.',
    },
    {
        key       => 's',
        name      => 'Scales',
        is_pause  => 0,
        is_adjust => 0,
        is_scales => 1,
        desc      => 'Scales count toward all active practice but not repertoire percentages. The Scales status is LOW below 5%, OK from 5% through 20%, or HIGH above 20% or after 30 minutes of Scales in the current session.',
    },
    {
        key             => 'h', # hearing / ear training; e is already Edit MP3
        name            => 'Ear training',
        is_pause        => 0,
        is_adjust       => 0,
        is_ear_training => 1,
        desc            => 'Ear training counts toward all active practice and daily rankings, but not repertoire percentages. Its status is LOW below 5%, OK from 5% through 20%, and HIGH above 20% of active practice. It can have its own MP3s and other media.',
    },
    {
        key       => 'p',
        name      => 'Pause',
        is_pause  => 1,
        is_adjust => 0,
        desc      => 'Pause is non-practice time. By default, pause time is excluded from the category percentage denominator.',
    },
    {
        key       => 'a',
        name      => 'Adjust',
        is_pause  => 0,
        is_adjust => 1,
        desc      => 'Adjust lets you manually add or subtract minutes from a category.',
    },
);

my %by_key  = map { $_->{key} => $_ } @options;
my %elapsed = map { $_->{key} => 0 } @options;

my $current_key = 'p';
my $running     = 1;

# session_start is the displayed wall-clock beginning of the session.
# session_elapsed_offset + (time - session_clock_anchor) is the elapsed session clock.
# Saving/reloading uses the elapsed session clock, so time while the script is closed
# is not accidentally counted.
my $session_start;
my $session_start_stamp;
my $session_elapsed_offset = 0;
my $session_clock_anchor   = time;
my $last_tick              = time;
my $last_message           = '';
my $activity_report_message = '';
# The exact song ID shown in the last rendered practice tip. Empty for
# reminders, non-song tips, and days when nothing can be suggested.
my $displayed_tip_song_id = '';

# Song timing runs alongside, never instead of, the normal category clock.
# Direct category keys clear the song selection, so unspecified practice
# remains category-only. These hashes are for the current session.
my $current_song_id = '';
my $current_song_title = '';
my %song_elapsed;
my %song_titles;
my %song_practice_starts;
my %song_last_practiced_epoch;

# An individual selection starts as provisional. Once it reaches 60 seconds,
# credit all its time (including the first minute) and one practice start.
# These fields survive /r so a 45-second selection can qualify after reload.
my $current_selection_seconds   = 0;
my $current_selection_qualified = 0;
my $current_selection_id        = 0;
my $selection_serial            = 0;

# A separate display-only clock for the current uninterrupted stretch after
# Pause/Resume.  Unlike the selection minimum, this resets on each unpause,
# but not for menus/media or a /r reload. It never changes practice totals.
my $current_since_unpaused_seconds = 0;
my $current_was_unpaused           = 0;

# The selection suspended by Pause. Keep the original song selection ID and
# accrued (possibly provisional) seconds so Pause/Resume does not create a
# second practice start or discard progress toward the 60-second minimum.
# These values also survive /r when the paused session has been saved.
my $resume_key                 = '';
my $resume_song_id             = '';
my $resume_song_title          = '';
my $resume_selection_seconds   = 0;
my $resume_selection_qualified = 0;
my $resume_selection_id        = 0;

# Chronological segments let the session viewer show when each category/song
# was practiced. Segment seconds are actual timed seconds, not wall time in
# menus or while the application was closed. Older state files can still load.
my @session_segments;
my $active_segment;
my $session_timeline_partial = 0;

# One-level undo. After a successful undo, a new practice selection is
# required before another undo is available. The lock survives save/reload.
my $undo_locked = 0;

sub fmt_stamp {
    my ($epoch) = @_;
    return strftime("%Y-%m-%d %H:%M:%S", localtime($epoch));
}

sub parse_session_start {
    my ($input) = @_;

    $input //= '';
    $input =~ s/^\s+//;
    $input =~ s/\s+$//;

    my $example = '2026-06-16 09:28:48';

    return (undef, "Blank input.")
        if $input eq '';

    if ($input !~ /^(\d{4})-(\d{2})-(\d{2})[ T](\d{2}):(\d{2}):(\d{2})$/) {
        return (
            undef,
            "Use this format exactly: YYYY-MM-DD HH:MM:SS\nExample: $example"
        );
    }

    my ($year, $mon, $day, $hour, $min, $sec) =
        ($1, $2, $3, $4, $5, $6);

    my $epoch;

    eval {
        $epoch = timelocal($sec, $min, $hour, $day, $mon - 1, $year);
    };

    if ($@) {
        return (
            undef,
            "That date/time could not be parsed.\nExample: $example"
        );
    }

    # Catch impossible dates that Perl may normalize, such as 2026-02-31.
    my $roundtrip = fmt_stamp($epoch);
    my $wanted    = "$year-$mon-$day $hour:$min:$sec";

    if ($roundtrip ne $wanted) {
        return (
            undef,
            "That is not a valid calendar date/time.\nExample: $example"
        );
    }

    if ($epoch > time) {
        return (
            undef,
            "The session start time cannot be in the future.\nExample: $example"
        );
    }

    return ($epoch, undef);
}

sub usage {
    return <<'USAGE';
Usage:
  perl practice_timer.pl /n
  perl practice_timer.pl /n "2026-06-16 09:28:48"
  perl practice_timer.pl /r

Options:
  /n    Start a new session.
        You may optionally provide a manual session-start time.

  /r    Reload the saved session from practice_timer_session.state.
        Do not provide a session-start time with /r.

Manual session-start time format:
  YYYY-MM-DD HH:MM:SS

Shortcuts:
  On the desktop, double-click "Practice Log", then in the resulting 
  window, launch the script as per "Usage:" above.

  Move the resulting icon to the first position of the task bar.  You
  can then bring the script to the forefront by pressing Win+1

Example:
  perl practice_timer.pl /n "2026-06-16 09:28:48"
USAGE
}

sub parse_startup_args {
    if (!@ARGV) {
        print usage();
        exit 1;
    }

    my $flag = shift @ARGV;
    $flag //= '';
    $flag = lc $flag;

    if ($flag eq '/n') {
        # Some Windows launchers already supply /n and then accidentally
        # append a second /n. Do not interpret that duplicate as a date.
        shift @ARGV while @ARGV && lc($ARGV[0]) eq '/n';
        my $start_input = @ARGV ? join(' ', @ARGV) : undef;
        return ('new', $start_input);
    }

    if ($flag eq '/r') {
        # Likewise tolerate a launcher accidentally passing /r twice.
        shift @ARGV while @ARGV && lc($ARGV[0]) eq '/r';
        if (@ARGV) {
            print "The /r flag reloads the saved session and does not accept a session-start time.\n\n";
            print usage();
            exit 1;
        }

        return ('reload', undef);
    }

    print "Unknown option: $flag\n\n";
    print usage();
    exit 1;
}

sub initial_session_start {
    my ($input) = @_;

    return time unless defined $input && length $input;

    my ($epoch, $err) = parse_session_start($input);

    if (!defined $epoch) {
        die
            "Invalid session-start time: $input\n\n" .
            "$err\n\n" .
            "Properly formatted example:\n" .
            "  perl practice_timer.pl /n \"2026-06-16 09:28:48\"\n";
    }

    return $epoch;
}

sub practice_options {
    # Historical saved/log category order (includes Theory). Do not remove y:
    # older TSVs are parsed by the number and positions of these columns.
    # Use repertoire_total() for the percentage denominator instead.
    return grep { !$_->{is_pause} && !$_->{is_adjust} && !$_->{is_scales} && !$_->{is_ear_training} } @options;
}

sub pause_key {
    for my $option (@options) {
        return $option->{key} if $option->{is_pause};
    }
    return;
}

sub scales_key {
    for my $option (@options) {
        return $option->{key} if $option->{is_scales};
    }
    return;
}

sub ear_training_key {
    for my $option (@options) {
        return $option->{key} if $option->{is_ear_training};
    }
    return;
}

sub is_supplemental_key {
    my ($key) = @_;
    return exists($by_key{$key}) &&
        ($by_key{$key}->{is_scales} || $by_key{$key}->{is_ear_training});
}

# Theory has its own media attachments like Scales and Ear training.
# Retired Jamming attachments remain on disk, untouched, for historical use.
sub media_category_owner {
    my ($key) = @_;
    return ($SCALES_ATTACHMENT_ID, 'Scales')
        if defined($key) && defined(scales_key()) && $key eq scales_key();
    return ($EAR_TRAINING_ATTACHMENT_ID, 'Ear training')
        if defined($key) && defined(ear_training_key()) && $key eq ear_training_key();
    return ($THEORY_ATTACHMENT_ID, 'Theory')
        if defined($key) && $key eq 'y';
    return (undef, undef);
}

sub is_media_activity_key {
    my ($key) = @_;
    my ($id) = media_category_owner($key);
    return defined($id) ? 1 : 0;
}

sub fmt_time {
    my ($seconds) = @_;
    $seconds = int($seconds + 0.5);
    $seconds = 0 if $seconds < 0;

    my $h = int($seconds / 3600);
    my $m = int(($seconds % 3600) / 60);
    my $s = $seconds % 60;

    return sprintf("%02d:%02d:%02d", $h, $m, $s);
}

sub decimal_hours {
    my ($seconds) = @_;
    $seconds //= 0;
    $seconds = 0 if $seconds < 0;

    return sprintf('%.2f', $seconds / 3600);
}

sub fmt_time_decimal {
    my ($seconds) = @_;
    return fmt_time($seconds) . ' (' . decimal_hours($seconds) . ' hours)';
}


sub parse_hms_time {
    my ($value) = @_;
    return undef unless defined $value;

    $value =~ s/^\s+//;
    $value =~ s/\s+$//;

    return undef unless $value =~ /^(\d+):([0-5]\d):([0-5]\d)$/;

    return ($1 * 3600) + ($2 * 60) + $3;
}

sub parse_log_stamp {
    my ($input) = @_;

    $input //= '';
    $input =~ s/^\s+//;
    $input =~ s/\s+$//;

    return (undef, 'Blank date/time.')
        if $input eq '';

    if ($input !~ /^(\d{4})-(\d{2})-(\d{2})[ T](\d{2}):(\d{2}):(\d{2})$/) {
        return (undef, 'Date/time was not in YYYY-MM-DD HH:MM:SS format.');
    }

    my ($year, $mon, $day, $hour, $min, $sec) =
        ($1, $2, $3, $4, $5, $6);

    my $epoch;

    eval {
        $epoch = timelocal($sec, $min, $hour, $day, $mon - 1, $year);
    };

    return (undef, 'Date/time could not be parsed.')
        if $@;

    # Catch impossible dates that Perl may normalize, such as 2026-02-31.
    my $roundtrip = fmt_stamp($epoch);
    my $wanted    = "$year-$mon-$day $hour:$min:$sec";

    return (undef, 'Date/time was not a valid calendar date/time.')
        if $roundtrip ne $wanted;

    return ($epoch, undef);
}


sub fmt_report_span {
    my ($seconds) = @_;
    $seconds = int(($seconds // 0) + 0.5);
    $seconds = 0 if $seconds < 0;

    my $days = int($seconds / 86400);
    my $rest = $seconds % 86400;

    return fmt_time($rest) if $days == 0;
    return $days . ' day' . ($days == 1 ? '' : 's') . ' ' . fmt_time($rest);
}

# Restore last real timed practice from the dedicated timestamp. On first
# installation, recover the latest non-Pause segment from the existing saved
# session, without modifying any saved logs or song totals.
sub initialize_last_practice_clock {
    my $now = time;
    if (open my $fh, '<', $LAST_PRACTICE_FILE) {
        my $line = <$fh> // '';
        if ($line =~ /\A(?:last_active_epoch=)?(\d+(?:\.\d+)?)\s*\z/ && $1 > 0 && $1 <= $now + 5) {
            $last_practice_epoch = 0 + $1;
            $last_practice_written_epoch = $last_practice_epoch;
        }
        # Optional second line; old one-line state files are still valid.
        while (my $extra = <$fh>) {
            if ($extra =~ /\Alast_idle_alert_for_epoch=(\d+(?:\.\d+)?)\s*\z/
                && $1 > 0 && $1 <= $now + 5) {
                $last_idle_alert_for_epoch = 0 + $1;
            }
        }
        close $fh;
    }

    return unless -e $STATE_FILE && open my $fh, '<', $STATE_FILE;
    my ($saved_epoch, $saved_key, $segment_epoch) = (0, '', 0);
    while (my $line = <$fh>) {
        $saved_epoch = 0 + $1 if $line =~ /^saved_at_epoch=(\d+(?:\.\d+)?)\s*$/;
        $saved_key = $1 if $line =~ /^current_key=([^\r\n]*)/;
        next unless $line =~ /^session_segment_\d+=(.*)/;
        my $segment = decode_session_segment($1);
        next unless $segment && ($segment->{seconds} // 0) > 0;
        my $key = $segment->{key};
        next if $by_key{$key}->{is_pause} || $by_key{$key}->{is_adjust};
        my $end = $segment->{end_epoch};
        $segment_epoch = $end if $end > $segment_epoch && $end <= $now + 5;
    }
    close $fh;
    # For older state files without timeline segments, saved_at is the best
    # available approximation if the saved selection was actively practicing.
    if (!$segment_epoch && $saved_key ne '' && exists($by_key{$saved_key})
        && !$by_key{$saved_key}->{is_pause} && !$by_key{$saved_key}->{is_adjust}) {
        $segment_epoch = $saved_epoch if $saved_epoch <= $now + 5;
    }
    $last_practice_epoch = $segment_epoch
        if $segment_epoch > $last_practice_epoch;
}

sub persist_last_practice_epoch {
    my ($force) = @_;
    return unless $last_practice_epoch > 0;
    return if !$force && $last_practice_epoch - $last_practice_written_epoch < 10;
    if (open my $fh, '>', $LAST_PRACTICE_FILE) {
        printf {$fh} "last_active_epoch=%.6f\n", $last_practice_epoch;
        printf {$fh} "last_idle_alert_for_epoch=%.6f\n", $last_idle_alert_for_epoch;
        if (close $fh) {
            $last_practice_written_epoch = $last_practice_epoch;
        }
    }
}

# A 10-minute warning is eligible only while idle, and only once for
# the particular last-practice timestamp. Practice resumption resets the
# marker in tick_current(), allowing a fresh warning after another 10 minutes.
sub idle_practice_alert_due {
    return 0 unless $last_practice_epoch > 0;
    return 0 if exists($by_key{$current_key})
        && !$by_key{$current_key}->{is_pause}
        && !$by_key{$current_key}->{is_adjust};
    return 0 if $last_idle_alert_for_epoch > 0
        && abs($last_idle_alert_for_epoch - $last_practice_epoch) < 0.01;
    return time - $last_practice_epoch > $IDLE_ALERT_AFTER_SECONDS ? 1 : 0;
}

sub maybe_flash_idle_practice_alert {
    return 0 unless idle_practice_alert_due();

    # Mark before displaying to avoid repeat alerts on the next redraw or
    # after a /r restart. This file also contains the existing idle clock.
    $last_idle_alert_for_epoch = $last_practice_epoch;
    persist_last_practice_epoch(1);

    clear_screen();
    my %message = (
        26 => 'TEN MINUTES SINCE LAST PRACTICE',
        28 => 'TIME TO PICK UP THE GUITAR!',
        30 => 'The timer returns in five seconds.',
    );
    for my $line (1 .. 40) {
        if (exists $message{$line}) {
            printf "XX %-68s XX\n", $message{$line};
        }
        else {
            print 'X' x 74, "\n";
        }
    }
    sleep($IDLE_ALERT_HOLD_SECONDS);
    return 1;
}

sub time_since_last_practice_label {
    # Any actively timed practice category means we're currently practicing.
    return '00:00:00' if exists($by_key{$current_key})
        && !$by_key{$current_key}->{is_pause}
        && !$by_key{$current_key}->{is_adjust};
    return 'N/A' unless $last_practice_epoch > 0;
    my $idle = time - $last_practice_epoch;
    return fmt_report_span($idle > 0 ? $idle : 0);
}

sub date_from_stamp_text {
    my ($stamp) = @_;
    return undef unless defined $stamp;

    return sprintf('%04d-%02d-%02d', $1, $2, $3)
        if $stamp =~ /^(\d{4})-(\d{2})-(\d{2})[ T]\d{2}:\d{2}:\d{2}$/;

    return undef;
}

sub month_key_from_date {
    my ($ymd) = @_;
    return undef unless defined $ymd;

    return sprintf('%04d-%02d', $1, $2)
        if $ymd =~ /^(\d{4})-(\d{2})-\d{2}$/;

    return undef;
}

sub next_month_key {
    my ($month_key) = @_;
    return undef unless defined $month_key && $month_key =~ /^(\d{4})-(\d{2})$/;

    my ($year, $mon) = ($1, $2);
    $mon++;

    if ($mon > 12) {
        $mon = 1;
        $year++;
    }

    return sprintf('%04d-%02d', $year, $mon);
}

sub month_key_le {
    my ($left, $right) = @_;
    return 0 unless defined $left && defined $right;
    return $left le $right;
}

sub days_in_month {
    my ($year, $mon) = @_;

    my $next_year = $year;
    my $next_mon  = $mon + 1;

    if ($next_mon > 12) {
        $next_mon = 1;
        $next_year++;
    }

    my $last_day_epoch = timelocal(0, 0, 0, 1, $next_mon - 1, $next_year) - 86400;
    return (localtime($last_day_epoch))[3];
}

sub format_calendar_hours {
    my ($seconds) = @_;
    $seconds //= 0;

    # Keep a three-character cell, but show a dash for past no-practice days.
    return ' - ' if $seconds <= 0;

    my $hours = $seconds / 3600;

    # Calendar cells are intentionally only three characters wide.
    # The requested maximum visible entry is 9.9 hours.
    $hours = 9.9 if $hours > 9.9;

    return sprintf('%3.1f', $hours);
}

# Count genuine calendar-day streaks from the same positive daily practice
# totals as the calendar and rankings. UTC day numbers handle weekends, months,
# leap years and daylight saving transitions without shifting local dates.
sub practice_streak_day_number {
    my ($date) = @_;
    return undef unless defined($date) && $date =~ /\A(\d{4})-(\d{2})-(\d{2})\z/;
    my ($year, $month, $day) = ($1, $2, $3);
    my $epoch = eval { timegm(0, 0, 0, $day, $month - 1, $year) };
    return undef if $@ || !defined $epoch;
    return undef unless strftime('%Y-%m-%d', gmtime($epoch)) eq $date;
    return int($epoch / 86400);
}

# The current streak is live if the last recorded day was today or yesterday.
# The record is the longest uninterrupted calendar-day run within the chosen
# statistics window. Equal-length record streaks favor the most recent run.
sub practice_streak_stats {
    my ($active_by_date, $today_ymd) = @_;
    my @dates = sort grep {
        /\A\d{4}-\d{2}-\d{2}\z/ && $_ le $today_ymd
            && statistics_include_date($_)
            && ($active_by_date->{$_} // 0) > 0
    } keys %$active_by_date;

    my ($run_days, $run_start, $run_end, $last_day_number) = (0, '', '', undef);
    my ($record_days, $record_start, $record_end) = (0, '', '');

    for my $date (@dates) {
        my $day_number = practice_streak_day_number($date);
        next unless defined $day_number;
        if (defined($last_day_number) && $day_number == $last_day_number + 1) {
            $run_days++;
        }
        else {
            $run_days = 1;
            $run_start = $date;
        }
        $run_end = $date;
        $last_day_number = $day_number;

        if ($run_days >= $record_days) {
            ($record_days, $record_start, $record_end) =
                ($run_days, $run_start, $run_end);
        }
    }

    my $today_number = practice_streak_day_number($today_ymd);
    my $current = defined($today_number) && defined($last_day_number)
        && $last_day_number >= $today_number - 1;

    return {
        current_days  => $current ? $run_days  : 0,
        current_start => $current ? $run_start : '',
        current_end   => $current ? $run_end   : '',
        record_days   => $record_days,
        record_start  => $record_start,
        record_end    => $record_end,
    };
}

sub print_practice_streaks {
    my ($out, $active_by_date, $today_ymd) = @_;
    my $stats = practice_streak_stats($active_by_date, $today_ymd);

    print $out "Practice days streak\n";
    print $out "--------------------\n";
    for my $item (
        ['Current streak', 'current'],
        ['Record streak',  'record'],
    ) {
        my ($label, $kind) = @$item;
        my $days = $stats->{$kind . '_days'};
        if ($days) {
            printf $out "%s: %d %s (%s to %s)\n",
                $label, $days, ($days == 1 ? 'day' : 'days'),
                $stats->{$kind . '_start'}, $stats->{$kind . '_end'};
        }
        else {
            print $out "$label: 0 days\n";
        }
    }
    print $out "A day counts only if it has positive recorded active practice.\n";
    print $out "A current streak remains active through yesterday until today is practiced.\n";
    print $out "Practice counts on its calendar date; dated category corrections count on their assigned date.\n\n";
}

sub print_practice_calendar {
    my ($out, $active_by_date) = @_;

    my @dates = sort keys %$active_by_date;
    return unless @dates;

    my $first_month = month_key_from_date($dates[0]);
    my $last_month  = month_key_from_date($dates[-1]);

    return unless defined $first_month && defined $last_month;

    print $out "\nPractice calendar\n";
    print $out "-----------------\n";
    print $out "Each day cell shows active practice (repertoire, Theory, Scales and Ear training) for that date. A dash means no recorded practice on/after the statistics start; dates before the cutoff and future dates are blank.\n";
    print $out "Date numbers are intentionally omitted; the hour value replaces the date number.\n";
    print $out "Earlier sessions without daily detail use their successive saved snapshots to estimate daily totals.\n";
    print $out "Values over 9.9 hours are shown as 9.9 to preserve the calendar layout.\n\n";

    my $month = $first_month;
    my $today_ymd = strftime('%Y-%m-%d', localtime(time));

    while (month_key_le($month, $last_month)) {
        my ($year, $mon) = $month =~ /^(\d{4})-(\d{2})$/;
        my $month_epoch = timelocal(0, 0, 0, 1, $mon - 1, $year);
        my $title = strftime('%B %Y', localtime($month_epoch));
        my $first_wday = (localtime($month_epoch))[6]; # 0 = Sunday
        my $days = days_in_month($year, $mon);

        print $out "$title\n";
        print $out "Sun Mon Tue Wed Thu Fri Sat\n";

        my $wday = 0;

        for (1 .. $first_wday) {
            print $out "    ";
            $wday++;
        }

        for my $day (1 .. $days) {
            my $ymd = sprintf('%04d-%02d-%02d', $year, $mon, $day);
            # Neither dates before the configured statistics start nor future
            # dates are missed-practice days. Leave those cells blank.
            my $cell = ($ymd gt $today_ymd || !statistics_include_date($ymd))
                ? '   ' : format_calendar_hours($active_by_date->{$ymd} // 0);

            print $out $cell;
            $wday++;

            if ($wday == 7) {
                print $out "\n";
                $wday = 0;
            }
            else {
                print $out " ";
            }
        }

        print $out "\n" if $wday != 0;
        print $out "\n";

        $month = next_month_key($month);
    }
}


# Rank TODAY's individual practice hours, not an average of days or windows.
# Displayed rank 1 is the MOST practiced day (1 of N = best).
# Percentages deliberately keep the existing higher-is-better scale, where
# the strongest day receives 100%. With equal durations, today is treated
# as the best/most-recent tied day. Input includes today and only practice days.
sub practice_day_rank {
    my ($today_seconds, $day_values) = @_;
    return (undef, undef, undef) unless @$day_values;

    my $count = scalar(@$day_values);
    my $days_better_than_today = scalar grep { $_ > $today_seconds } @$day_values;
    my $descending_rank = $days_better_than_today + 1;
    my $percentile = 100 * ($count - $days_better_than_today) / $count;
    return ($descending_rank, $count, $percentile); # Display truncates whole percent.
}

# The lowest possible percentile only says that today's practice currently
# ranks last in that sample.  Display TBD there until the day improves enough
# to pass another day; this changes only presentation, never the rank maths.
# The minimum must be unique: equal-time ties already favor today.
sub practice_percentile_display {
    my ($percentile, $rank, $count, $show_percent_sign, $unavailable) = @_;
    return $unavailable unless defined $percentile;
    return 'TBD' if defined($rank) && defined($count) && $count > 1
        && $rank == $count;
    return sprintf($show_percent_sign ? '%d%%' : '%d', $percentile);
}

# Render the main-screen 7/14-day rankings as ordinals rather than
# percentile scores. Even the last-place day has a valid rank.
sub practice_rank_ordinal {
    my ($rank) = @_;
    return 'N/A' unless defined $rank && $rank > 0;
    my $ending = ($rank % 100 >= 11 && $rank % 100 <= 13) ? 'th'
        : $rank % 10 == 1 ? 'st'
        : $rank % 10 == 2 ? 'nd'
        : $rank % 10 == 3 ? 'rd' : 'th';
    return $rank . $ending;
}

# Each percentile ranks the CURRENT DAY among individual practiced days:
#   All: every positive practice day through today, INCLUDING today.
#   7 Day: the seven most recent positive practice days, INCLUDING today.
#   14 Day: the fourteen most recent positive practice days, INCLUDING today.
# Non-practice days never appear in any sample. Before a complete 7- or
# 14-practice-day sample exists, the respective result is N/A. Every
# window uses exact daily seconds rather than seven-/fourteen-day averages.
sub practice_percentile_stats {
    my ($active_by_date, $today_ymd) = @_;

    my @practice_days = sort grep {
        /^\d{4}-\d{2}-\d{2}$/ && $_ le $today_ymd
            && statistics_include_date($_)
            && defined($active_by_date->{$_}) && $active_by_date->{$_} > 0
    } keys %$active_by_date;
    return undef unless @practice_days;

    my $today_seconds = $active_by_date->{$today_ymd} // 0;
    $today_seconds = 0 if $today_seconds <= 0;
    my $today_has_practice = $today_seconds > 0;

    my @past_days = grep { $_ lt $today_ymd } @practice_days;
    my ($best_day_seconds, $best_day_date) = (undef, undef);
    for my $date (@past_days) {
        my $seconds = $active_by_date->{$date};
        if (!defined($best_day_seconds) || $seconds >= $best_day_seconds) {
            $best_day_seconds = $seconds;
            $best_day_date    = $date;
        }
    }

    my ($all_rank, $all_count, $all_percentile) = (undef, undef, undef);
    if ($today_has_practice) {
        my @all_values = map { $active_by_date->{$_} } @practice_days;
        ($all_rank, $all_count, $all_percentile) =
            practice_day_rank($today_seconds, \@all_values);
    }

    my (@recent_seven_dates, $week_rank, $week_count, $week_percentile);
    my ($best_recent_seconds, $best_recent_date) = (undef, undef);
    if ($today_has_practice && @practice_days >= 7) {
        @recent_seven_dates = @practice_days[-7 .. -1];
        my @seven_values = map { $active_by_date->{$_} } @recent_seven_dates;
        ($week_rank, $week_count, $week_percentile) =
            practice_day_rank($today_seconds, \@seven_values);

        # For encouragement, the target to beat is the strongest of the
        # OTHER six days, not an average or a previous moving-window sum.
        for my $date (@recent_seven_dates[0 .. 5]) {
            my $seconds = $active_by_date->{$date};
            if (!defined($best_recent_seconds) || $seconds >= $best_recent_seconds) {
                $best_recent_seconds = $seconds;
                $best_recent_date    = $date;
            }
        }
    }

    # The 14 Day rank is analogous to 7 Day: today's individual hours
    # compared with the fourteen most recent days with actual practice.
    # We do not use fourteen consecutive calendar days or an arithmetic mean.
    my (@recent_fourteen_dates, $fortnight_rank, $fortnight_count, $fortnight_percentile);
    my ($best_recent_fourteen_seconds, $best_recent_fourteen_date) = (undef, undef);
    if ($today_has_practice && @practice_days >= 14) {
        @recent_fourteen_dates = @practice_days[-14 .. -1];
        my @fourteen_values = map { $active_by_date->{$_} } @recent_fourteen_dates;
        ($fortnight_rank, $fortnight_count, $fortnight_percentile) =
            practice_day_rank($today_seconds, \@fourteen_values);

        for my $date (@recent_fourteen_dates[0 .. 12]) {
            my $seconds = $active_by_date->{$date};
            if (!defined($best_recent_fourteen_seconds)
                || $seconds >= $best_recent_fourteen_seconds) {
                $best_recent_fourteen_seconds = $seconds;
                $best_recent_fourteen_date = $date;
            }
        }
    }

    return {
        today                   => $today_ymd,
        today_seconds           => $today_seconds,
        today_has_practice      => $today_has_practice,
        practice_day_count      => scalar(@practice_days),
        prior_day_count         => scalar(@past_days),
        daily_percentile        => $all_percentile,
        all_rank                => $all_rank,
        all_count               => $all_count,
        best_prior_day_secs     => $best_day_seconds,
        best_prior_day_date     => $best_day_date,
        week_percentile         => $week_percentile,
        week_rank               => $week_rank,
        week_count              => $week_count,
        recent_seven_dates      => \@recent_seven_dates,
        best_recent_day_secs    => $best_recent_seconds,
        best_recent_day_date    => $best_recent_date,
        fortnight_percentile    => $fortnight_percentile,
        fortnight_rank          => $fortnight_rank,
        fortnight_count         => $fortnight_count,
        recent_fourteen_dates   => \@recent_fourteen_dates,
        best_recent_14_secs     => $best_recent_fourteen_seconds,
        best_recent_14_date     => $best_recent_fourteen_date,
    };
}

sub print_practice_percentiles {
    my ($out, $active_by_date, $today_ymd) = @_;
    my $stats = practice_percentile_stats($active_by_date, $today_ymd);

    print $out "Practice-day rankings (practice day: $today_ymd)\n";
    print $out "------------------------------------------\n";

    if (!$stats) {
        print $out "No recorded practice days through today. Rankings unavailable.\n\n";
        return;
    }

    my $daily_rank = practice_percentile_display(
        $stats->{daily_percentile}, $stats->{all_rank}, $stats->{all_count},
        0, 'N/A (no practice recorded today)');
    print $out "Percentile of hours practiced, all: $daily_rank\n";
    if (defined $stats->{all_rank}) {
        printf $out "  Today: %.2f hours; rank %d of %d practice days (including today).\n",
            $stats->{today_seconds} / 3600,
            $stats->{all_rank}, $stats->{all_count};
    }
    if (defined $stats->{best_prior_day_secs}) {
        printf $out "  Previous daily best: %.2f hours (%s).\n",
            $stats->{best_prior_day_secs} / 3600, $stats->{best_prior_day_date};
        if ($stats->{today_has_practice}
            && $stats->{today_seconds} > $stats->{best_prior_day_secs}) {
            print $out "  New daily practice record today!\n";
        }
        else {
            my $needed = $stats->{best_prior_day_secs} - $stats->{today_seconds} + 1;
            print $out "  To beat the daily best: " . fmt_time($needed) . " more today.\n";
        }
    }

    my $week_rank = practice_percentile_display(
        $stats->{week_percentile}, $stats->{week_rank}, $stats->{week_count},
        0, !$stats->{today_has_practice}
            ? 'N/A (no practice recorded today)'
            : 'N/A (fewer than seven practice days)');
    print $out "Percentile of hours practiced, last 7 practice days: $week_rank\n";
    if (defined $stats->{week_rank}) {
        printf $out "  Today ranks %d of 7 individual practice days (including today).\n",
            $stats->{week_rank};
        printf $out "  Best of the preceding six: %.2f hours (%s).\n",
            $stats->{best_recent_day_secs} / 3600, $stats->{best_recent_day_date};
        if ($stats->{today_seconds} > $stats->{best_recent_day_secs}) {
            print $out "  Highest practice day of your latest seven!\n";
        }
        else {
            my $needed = $stats->{best_recent_day_secs} - $stats->{today_seconds} + 1;
            print $out "  To beat the best of those six: " . fmt_time($needed) . " more today.\n";
        }
    }
    my $fortnight_rank = practice_percentile_display(
        $stats->{fortnight_percentile}, $stats->{fortnight_rank},
        $stats->{fortnight_count}, 0,
        !$stats->{today_has_practice}
            ? 'N/A (no practice recorded today)'
            : 'N/A (fewer than fourteen practice days)');
    print $out "Percentile of hours practiced, last 14 practice days: $fortnight_rank\n";
    if (defined $stats->{fortnight_rank}) {
        printf $out "  Today ranks %d of 14 individual practice days (including today).\n",
            $stats->{fortnight_rank};
        printf $out "  Best of the preceding thirteen: %.2f hours (%s).\n",
            $stats->{best_recent_14_secs} / 3600, $stats->{best_recent_14_date};
        if ($stats->{today_seconds} > $stats->{best_recent_14_secs}) {
            print $out "  Highest practice day of your latest fourteen!\n";
        }
        else {
            my $needed = $stats->{best_recent_14_secs} - $stats->{today_seconds} + 1;
            print $out "  To beat the best of those thirteen: " . fmt_time($needed) . " more today.\n";
        }
    }
    print $out "Ranks compare today's individual daily hours; no moving averages are used.\n";
    print $out "Displayed ranks are descending (1 is best); percentile scores remain higher-is-better.\n";
    print $out "Only days with positive practice count. Ties favor today's (most recent) date.\n";
    print $out "Practice days use local calendar dates (midnight to midnight); View refreshes all rankings.\n\n";
}

sub number_or_zero {
    my ($value) = @_;
    return 0 unless defined $value;
    return 0 unless $value =~ /^[+-]?(?:\d+(?:\.\d*)?|\.\d+)$/;
    return 0 + $value;
}

sub session_elapsed {
    return $session_elapsed_offset + (time - $session_clock_anchor);
}

sub active_total {
    # Historical log layout: all non-Pause, non-supplemental categories,
    # including Theory. Keep this unchanged so old TSV rows remain readable.
    my $total = 0;

    for my $option (practice_options()) {
        $total += $elapsed{ $option->{key} };
    }

    return $total;
}

sub theory_total {
    return $elapsed{y} // 0;
}

sub repertoire_total {
    # Only the song/repertoire categories share the 100% distribution.
    # Theory, Scales and Ear training still count as active practice.
    return active_total() - theory_total();
}

sub scales_total {
    my $key = scales_key();
    return 0 unless defined $key;
    return $elapsed{$key} // 0;
}

sub ear_training_total {
    my $key = ear_training_key();
    return 0 unless defined $key;
    return $elapsed{$key} // 0;
}

sub reported_active_total {
    # Total reported practice includes the target categories, Scales, and Ear training.
    # It is NOT used as the denominator for category percentages.
    return active_total() + scales_total() + ear_training_total();
}

sub practice_session_percent {
    my $session_elapsed = session_elapsed();
    return 0 if $session_elapsed <= 0;
    return 100 * active_total() / $session_elapsed;
}

sub practice_session_percent_whole {
    return int(practice_session_percent() + 0.5);
}

sub percent_for {
    my ($key) = @_;

    return 0 if $key eq 'y'; # Theory is never a repertoire percentage.
    my $denom = $COUNT_PAUSE_IN_PERCENT
        ? session_elapsed() - theory_total()
        : repertoire_total();

    return 0 if $denom <= 0;
    return 100 * $elapsed{$key} / $denom;
}

sub percent_whole {
    my ($key) = @_;
    return int(percent_for($key) + 0.5);
}

# Supplemental percentage/status uses a different denominator from repertoire.
sub supplemental_percent_for {
    my ($key) = @_;
    my $total = reported_active_total();
    return 0 if $total <= 0;
    return 100 * ($elapsed{$key} // 0) / $total;
}

sub supplemental_status_for {
    my ($option) = @_;
    my $key = $option->{key};
    return 'HIGH' if $option->{is_scales}
        && ($elapsed{$key} // 0) > $SCALES_HIGH_AFTER_SECONDS;

    # Use the same whole percentage that appears on the main screen.
    my $pct_whole = int(supplemental_percent_for($key) + 0.5);
    return 'LOW'  if $pct_whole < $SUPPLEMENTAL_TARGET_MIN_PERCENT;
    return 'HIGH' if $pct_whole > $SUPPLEMENTAL_TARGET_MAX_PERCENT;
    return 'OK';
}

sub target_label {
    my ($option) = @_;

    if ($option->{is_scales}) {
        return "$SUPPLEMENTAL_TARGET_MIN_PERCENT-$SUPPLEMENTAL_TARGET_MAX_PERCENT% / 30m";
    }
    if ($option->{is_ear_training}) {
        return "$SUPPLEMENTAL_TARGET_MIN_PERCENT-$SUPPLEMENTAL_TARGET_MAX_PERCENT%";
    }
    return '10-20m/day' if ($option->{key} // '') eq 'y';
    return '-' unless defined $option->{target_min} && defined $option->{target_max};

    return $option->{target_min} . '%'
        if $option->{target_min} == $option->{target_max};

    return $option->{target_min} . '-' . $option->{target_max} . '%';
}

sub status_for {
    my ($option, $pct) = @_;

    return '' unless defined $option->{target_min} && defined $option->{target_max};

    # A 0% target means no scheduled requirement, not an upper limit.
    # Show a neutral status even when time is spent in this category.
    return '-' if $option->{target_min} == 0 && $option->{target_max} == 0;

    # Use the same rounded whole-number percent shown on screen.
    # This prevents cases where 19.84 displays as 20% but still tests as LOW.
    my $pct_whole = int($pct + 0.5);

    return 'LOW'  if $pct_whole < $option->{target_min};
    return 'HIGH' if $pct_whole > $option->{target_max};
    return 'OK';
}

sub log_name {
    my ($name) = @_;
    $name = lc $name;
    $name =~ s/[^a-z0-9]+/_/g;
    $name =~ s/^_//;
    $name =~ s/_$//;
    return $name;
}

# Clearing for a menu/alert invalidates every previous row.  The ordinary
# ten-second main-screen repaint NEVER calls this unless its frame is invalid.
sub invalidate_main_screen {
    $main_screen_cache_valid = 0;
    @main_screen_last_lines = ();
    $main_screen_last_geometry = '';
    $main_screen_status_first_row = -1;
    $main_screen_status_row_count = 0;
    $main_screen_song_first_row = -1;
    $main_screen_song_row_count = 0;
    $main_screen_pending_first_row = -1;
    $main_screen_pending_row_count = 0;
    $main_screen_song_line_present = 0;
    $main_screen_pending_line_present = 0;
}

sub clear_screen {
    invalidate_main_screen();
    if ($^O eq 'MSWin32') {
        # The dashboard writes through Win32::Console, so clear through that
        # SAME output handle.  A separate `system('cls')` is not reliable for
        # restoring cells overwritten by a normal STDOUT media prompt.
        my $out = main_screen_win32_output();
        if ($out) {
            my $cleared = eval { $out->Cls() };
            if (defined $cleared) {
                # Menus and the media question use normal line input.
                # Keep the hardware cursor visible for those prompts.
                eval { $out->Cursor(-1, -1, -1, 1) };
                return;
            }
        }
        system('cls');
    }
    else {
        system('clear');
    }
}

# The same Win32::Console distribution already used by PracticeKeys for F1-F12
# also gives us direct, absolute-position character writes. Unlike ANSI escape
# sequences, this works in classic Windows Command Prompt with VT turned OFF.
sub main_screen_win32_output {
    return $win_console_output if $win_console_output_checked;
    $win_console_output_checked = 1;
    return undef unless $^O eq 'MSWin32';
    my $ok = eval {
        require Win32::Console;
        my $handle = Win32::Console::STD_OUTPUT_HANDLE();
        my $out = Win32::Console->new($handle);
        die 'No console output handle' unless $out;
        my @info = $out->Info();
        die 'Unable to inspect console size' unless @info >= 9;
        $win_console_output = $out;
        1;
    };
    $win_console_output = undef unless $ok;
    return $win_console_output;
}

# Build rows exactly as the old Perl print-based display would, except split
# long lines at the real console width so an update cannot wrap or scroll.
sub main_screen_physical_lines {
    my ($text, $width) = @_;
    $width = 80 unless $width && $width > 1;
    # Leave the last column alone to avoid automatic wrap in VT terminals.
    my $usable = $width - 1;
    my @logical = split /\n/, $text, -1;
    pop @logical if @logical && $logical[-1] eq '';
    my @physical;
    for my $line (@logical) {
        $line =~ s/\r\z//;
        if (!length $line) {
            push @physical, '';
            next;
        }
        while (length($line) > $usable) {
            push @physical, substr($line, 0, $usable, '');
        }
        push @physical, $line;
    }
    return @physical;
}

sub main_screen_terminal_geometry {
    my $out = main_screen_win32_output();
    if ($out) {
        my @info = eval { $out->Info() };
        # Info: buffer columns/rows; cursor; attributes; visible window
        # left/top/right/bottom. Rows are zero-based in Win32::Console.
        if (@info >= 9) {
            my ($width, $buffer_rows, undef, undef, undef, undef,
                $top, undef, $bottom) = @info;
            if ($width > 1 && $buffer_rows > 0 && $top >= 0
                && $bottom >= $top) {
                return ('win32', $out, $width, $bottom - $top + 1,
                    $top, $buffer_rows);
            }
        }
    }
    if ($^O ne 'MSWin32' && -t STDOUT) {
        my ($width, $height) = eval { Term::ReadKey::GetTerminalSize() };
        if ($width && $height && $width > 1 && $height > 0) {
            return ('ansi', undef, $width, $height, 0, $height);
        }
    }
    return ('plain', undef, 0, 0, 0, 0);
}

sub present_main_screen {
    my ($frame) = @_;
    my ($backend, $out, $width, $height, $top, $buffer_height)
        = main_screen_terminal_geometry();
    my @lines = $backend eq 'plain'
        ? () : main_screen_physical_lines($frame, $width);
    my $clipped_from_top = 0;
    # A short console formerly scrolled while printing the whole page: the
    # visible part was the LAST windowful of lines. Keep that same view while
    # updating it in place (rather than falling back to flickering cls).
    if ($backend ne 'plain' && @lines > $height) {
        $clipped_from_top = @lines - $height;
        splice @lines, 0, $clipped_from_top;
    }
    my $geometry = join(':', $backend, $width, $height, $top);

    # No native cursor-writing API? Keep the old functional print renderer.
    # It may flicker, but avoids printing raw ANSI escapes in classic cmd.exe.
    if ($backend eq 'plain'
        || ($backend eq 'win32' && $top + @lines > $buffer_height)) {
        clear_screen();
        print $frame;
        return;
    }

    my $full = !$main_screen_cache_valid
        || $geometry ne $main_screen_last_geometry;
    if ($full) {
        clear_screen();  # Full repaint only on startup/menu/resize/alert.
        # cls may have repositioned the viewport. Re-query its origin.
        if ($backend eq 'win32') {
            my @now = eval { $out->Info() };
            if (@now >= 9) {
                $top = $now[6];
                $geometry = join(':', $backend, $width, $height, $top);
            }
        }
    }

    my $max_rows = @lines > @main_screen_last_lines
        ? scalar(@lines) : scalar(@main_screen_last_lines);
    if ($backend eq 'win32') {
        for my $row (0 .. $max_rows - 1) {
            my $new = $lines[$row] // '';
            my $prior = $full ? '' : ($main_screen_last_lines[$row] // '');
            next if !$full && $new eq $prior;
            # Write ONE string without first blanking the row. Pad only if
            # its old text was longer: no flash even within a changed line.
            my $write = $new;
            if ($full) {
                # Full repaints must overwrite any text put into the row by
                # a direct STDOUT prompt, not just what our frame cache knows.
                # Leave the last column untouched to avoid terminal wrapping.
                $write .= ' ' x (($width - 1) - length($write));
            }
            else {
                $write .= ' ' x (length($prior) - length($new))
                    if length($prior) > length($new);
            }
            next unless length $write;
            # WriteChar changes cells in place without moving the cursor.
            my $written = eval { $out->WriteChar($write, 0, $top + $row) };
            if (!defined($written) || $written < length($write)) {
                # Broken output handle? Restore correctness using old output.
                $win_console_output = undef;
                $win_console_output_checked = 1;
                clear_screen();
                print $frame;
                return;
            }
        }
    }
    else { # A normal VT terminal (Linux/macOS), not Windows cmd.exe.
        my $changes = '';
        for my $row (0 .. $max_rows - 1) {
            my $new = $lines[$row] // '';
            next if !$full && $new eq ($main_screen_last_lines[$row] // '');
            $changes .= sprintf("\e[%d;1H\e[2K%s", $row + 1, $new);
        }
        # One buffered print per refresh; no newlines and no scrolling.
        print "\e[?25l$changes\e[?25h" if length $changes;
    }
    if ($backend eq 'win32') {
        # WriteChar updates cells but never moves or hides the cursor.  With
        # the last interactive prompt at the top of the buffer, the cursor
        # otherwise remains over the dashboard status line indefinitely.
        # clear_screen() restores visibility for the next interactive menu.
        eval { $out->Cursor(-1, -1, -1, 0) };
    }
    @main_screen_last_lines = @lines;
    $main_screen_cache_valid = 1;
    $main_screen_last_geometry = $geometry;

    # Locate the second logical line (the status line) in PHYSICAL rows.
    # Do this from the actual buffered frame rather than assuming that a
    # terminal is wide enough for the status line to occupy exactly one row.
    $main_screen_status_first_row = -1;
    $main_screen_status_row_count = 0;
    my ($separator, $status) = split /\n/, $frame, 3;
    if (defined $status) {
        my @before = main_screen_physical_lines($separator . "\n", $width);
        my @status_rows = main_screen_physical_lines($status . "\n", $width);
        my $first = scalar(@before) - $clipped_from_top;
        if ($first >= 0 && $first + @status_rows <= @lines) {
            $main_screen_status_first_row = $first;
            $main_screen_status_row_count = scalar @status_rows;
        }
    }

    # Locate the live selected-song timers in the actual rendered frame. The
    # optional memory-review reminder and wrapped song titles shift their rows,
    # so never rely on fixed console coordinates. Reset the mapping EVERY
    # repaint: pending disappears immediately after a song qualifies.
    $main_screen_song_first_row = -1;
    $main_screen_song_row_count = 0;
    $main_screen_pending_first_row = -1;
    $main_screen_pending_row_count = 0;
    $main_screen_song_line_present = 0;
    $main_screen_pending_line_present = 0;
    my @logical = split /\n/, $frame, -1;
    pop @logical if @logical && $logical[-1] eq '';
    my $physical_offset = 0;
    for my $line (@logical) {
        my @physical = main_screen_physical_lines($line . "\n", $width);
        my $first = $physical_offset - $clipped_from_top;
        my $fully_visible = $first >= 0 && $first + @physical <= @lines;
        if ($line =~ /^Song this session: /) {
            $main_screen_song_line_present = 1;
            if ($fully_visible) {
                $main_screen_song_first_row = $first;
                $main_screen_song_row_count = scalar @physical;
            }
        }
        elsif ($line =~ /^Selection pending: /) {
            $main_screen_pending_line_present = 1;
            if ($fully_visible) {
                $main_screen_pending_first_row = $first;
                $main_screen_pending_row_count = scalar @physical;
            }
        }
        $physical_offset += scalar @physical;
    }
}

# One-second update: touch ONLY the status clock and selected-song clock rows.
# No historical TSV lookups or full-frame generation unless the song selection
# changes its shape (the pending line disappears at the 60-second threshold).
sub refresh_main_status_line {
    # The ten-minute idle warning is checked on this fast cadence too.
    if (idle_practice_alert_due()) {
        render();
        return;
    }

    return unless $main_screen_cache_valid;

    # At sixty seconds, "Selection pending" is replaced by the qualified song
    # clock. A full selective render removes that row safely and immediately.
    my $has_song = length($current_song_id) ? 1 : 0;
    my $has_pending = $has_song && !$current_selection_qualified ? 1 : 0;
    if ($has_song != $main_screen_song_line_present
        || $has_pending != $main_screen_pending_line_present) {
        render();
        return;
    }

    my ($backend, $out, $width, $height, $top, $buffer_height)
        = main_screen_terminal_geometry();
    return if $backend eq 'plain';
    my $geometry = join(':', $backend, $width, $height, $top);
    if ($geometry ne $main_screen_last_geometry) {
        render();
        return;
    }

    my @clocks = (
        [$main_screen_status_first_row, $main_screen_status_row_count,
            main_screen_status_line(1)],
    );
    push @clocks, [$main_screen_song_first_row,
        $main_screen_song_row_count, main_screen_song_session_line()]
        if $has_song;
    push @clocks, [$main_screen_pending_first_row,
        $main_screen_pending_row_count, main_screen_selection_pending_line()]
        if $has_pending;

    # Validate row counts and locations BEFORE writing anything. If the text
    # wraps differently, the full selective renderer must adjust all offsets.
    my @changes;
    for my $clock (@clocks) {
        my ($first, $count, $text) = @$clock;
        next if $first < 0;  # A top-clipped clock is not visible.
        my @new = main_screen_physical_lines($text . "\n", $width);
        if (@new != $count || $first + @new > @main_screen_last_lines
            || ($backend eq 'win32' && $top + $first + @new > $buffer_height)) {
            render();
            return;
        }
        for my $i (0 .. $#new) {
            my $row = $first + $i;
            my $prior = $main_screen_last_lines[$row] // '';
            next if $new[$i] eq $prior;
            push @changes, [$row, $new[$i], $prior];
        }
    }

    if ($backend eq 'win32') {
        for my $change (@changes) {
            my ($row, $new, $prior) = @$change;
            # Replace a row in one write. Pad shorter values so stale digits
            # vanish without first blanking the row (which would flicker).
            my $write = $new;
            $write .= ' ' x (length($prior) - length($new))
                if length($prior) > length($new);
            my $written = eval { $out->WriteChar($write, 0, $top + $row) };
            if (!defined($written) || $written < length($write)) {
                render();
                return;
            }
            $main_screen_last_lines[$row] = $new;
        }
    }
    else { # ANSI: buffered print for just the changed clock rows.
        my $output = '';
        for my $change (@changes) {
            my ($row, $new) = @$change;
            $output .= sprintf("\e[%d;1H\e[2K%s", $row + 1, $new);
            $main_screen_last_lines[$row] = $new;
        }
        print "\e[?25l$output\e[?25h" if length $output;
    }
}

sub tick_current {
    my $now = time;
    my $dt  = $now - $last_tick;
    $last_tick = $now;

    return if $dt <= 0;
    return unless exists $elapsed{$current_key};
    return if $by_key{$current_key}->{is_adjust};

    $elapsed{$current_key} += $dt;

    if (!$by_key{$current_key}->{is_pause}) {
        # Even a brief return to actual timed practice starts a new idle
        # stretch. Persist that reset immediately if an alert had fired.
        my $reset_idle_alert = $last_idle_alert_for_epoch > 0;
        $last_idle_alert_for_epoch = 0;
        $last_practice_epoch = $now;
        persist_last_practice_epoch($reset_idle_alert);
    }

    $active_segment->{seconds} += $dt if defined $active_segment;

    if (length $current_song_id
        && exists $by_key{$current_key}
        && !$by_key{$current_key}->{is_pause}
        && !is_supplemental_key($current_key)) {
        $current_selection_seconds += $dt;
        $current_since_unpaused_seconds += $dt if $current_was_unpaused;
        if (!$current_selection_qualified
            && $current_selection_seconds >= $MIN_SONG_SELECTION_SECONDS) {
            # The first minute counts only once the selection qualifies.
            $song_elapsed{$current_song_id} += $current_selection_seconds;
            $song_practice_starts{$current_song_id}++;
            $current_selection_qualified = 1;
        }
        elsif ($current_selection_qualified) {
            $song_elapsed{$current_song_id} += $dt;
        }
        $song_last_practiced_epoch{$current_song_id} = $now
            if $current_selection_qualified;
    }
}

sub clear_current_song {
    $current_song_id = '';
    $current_song_title = '';
    $current_selection_seconds = 0;
    $current_selection_qualified = 0;
    $current_selection_id = 0;
    $current_since_unpaused_seconds = 0;
    $current_was_unpaused = 0;
}

sub clear_resume_selection {
    $resume_key = '';
    $resume_song_id = '';
    $resume_song_title = '';
    $resume_selection_seconds = 0;
    $resume_selection_qualified = 0;
    $resume_selection_id = 0;
}

# The caller closes the old timeline segment and starts the next one.
# Pausing suspends the existing selection; it must not start another one.
sub toggle_pause_selection {
    if ($current_key ne pause_key()) {
        $resume_key = $current_key;
        $resume_song_id = $current_song_id;
        $resume_song_title = $current_song_title;
        $resume_selection_seconds = $current_selection_seconds;
        $resume_selection_qualified = $current_selection_qualified;
        $resume_selection_id = $current_selection_id;
        $current_key = pause_key();
        clear_current_song();
        $last_message = "Paused [$resume_key] "
            . (length($resume_song_title) ? $resume_song_title : $by_key{$resume_key}->{name})
            . '. Press p(r) again to resume.';
        return 1;
    }

    if (!length $resume_key || !exists $by_key{$resume_key}
        || $by_key{$resume_key}->{is_pause}
        || $by_key{$resume_key}->{is_adjust}
        || $by_key{$resume_key}->{is_retired}) {
        clear_resume_selection();
        $last_message = 'Nothing to resume yet. Select a song, Scales, Ear training, or practice category.';
        return 0;
    }
    $current_key = $resume_key;
    $current_song_id = $resume_song_id;
    $current_song_title = $resume_song_title;
    $current_selection_seconds = $resume_selection_seconds;
    $current_selection_qualified = $resume_selection_qualified;
    $current_selection_id = $resume_selection_id;
    # Only a real unpause starts this clock, not a menu return or /r.
    $current_was_unpaused = length($current_song_id) ? 1 : 0;
    $current_since_unpaused_seconds = 0;
    clear_resume_selection();
    $last_message = 'Resumed [$current_key] '
        . (length($current_song_title) ? $current_song_title : $by_key{$current_key}->{name})
        . '.';
    return 1;
}

# Start a new chronological segment whenever a timed selection resumes.
sub start_session_segment {
    return unless exists $by_key{$current_key};
    return if $by_key{$current_key}->{is_adjust};
    return if defined $active_segment;

    $active_segment = {
        start_epoch => time,
        key => $current_key,
        song_id => $current_song_id,
        song_title => $current_song_title,
        selection_id => $current_selection_id,
        seconds => 0,
    };
}

sub finish_session_segment {
    return unless defined $active_segment;
    my $finished = $active_segment;
    $active_segment = undef;
    $finished->{end_epoch} = time;
    push @session_segments, $finished if $finished->{seconds} > 0.001;
}

# The final (live) segment is written as a snapshot, without closing it.
# Loading a snapshot begins a fresh segment at reload time, rather than
# counting hours or days when the program was not running.
sub session_segments_snapshot {
    my @segments = @session_segments;
    if (defined $active_segment && $active_segment->{seconds} > 0.001) {
        push @segments, { %$active_segment, end_epoch => time };
    }
    return @segments;
}

# Exact per-calendar-day active practice for this (possibly multi-day) session.
# Persist the breakdown in the existing session snapshot TSV. The older TSV
# columns remain unchanged, and pre-upgrade rows remain readable. Local midnight
# (including DST transitions), not /n, is the boundary for the calendar.
sub session_active_seconds_by_local_date {
    my %days;
    for my $segment (session_segments_snapshot()) {
        my $key = $segment->{key} // '';
        next unless exists $by_key{$key};
        next if $by_key{$key}->{is_pause} || $by_key{$key}->{is_adjust};
        my $seconds = $segment->{seconds} // 0;
        next unless $seconds > 0;
        my $from = $segment->{start_epoch} // 0;
        my $to = $segment->{end_epoch} // $from;
        next unless $from > 0 && $to > $from;
        my $duration = $to - $from;
        my $cursor = $from;
        while ($cursor < $to) {
            my @lt = localtime($cursor);
            my $date = strftime('%Y-%m-%d', @lt);
            # Noon plus 24h gets the next *date* even across DST changes.
            my $local_noon = timelocal(0, 0, 12, $lt[3], $lt[4], $lt[5]);
            my @next_day = localtime($local_noon + 86400);
            my $next_midnight = timelocal(0, 0, 0,
                $next_day[3], $next_day[4], $next_day[5]);
            my $edge = $next_midnight < $to ? $next_midnight : $to;
            last if $edge <= $cursor;
            $days{$date} += $seconds * ($edge - $cursor) / $duration;
            $cursor = $edge;
        }
    }

    # Manual adjustments can change category totals without a timed segment.
    # Reconcile them on the date of the save, keeping the daily sum equal to the
    # session's actual totals without losing any history or double counting.
    my $expected = reported_active_total();
    my $observed = 0;
    $observed += $_ for values %days;
    my $difference = $expected - $observed;
    if ($difference > 0.01) {
        $days{strftime('%Y-%m-%d', localtime(time))} += $difference;
    }
    elsif ($difference < -0.01) {
        for my $date (reverse sort keys %days) {
            my $remove = -$difference < $days{$date} ? -$difference : $days{$date};
            $days{$date} -= $remove;
            $difference += $remove;
            last if $difference >= -0.01;
        }
    }
    return \%days;
}

# Exact Theory time in each local calendar day of the current (possibly
# multi-day) session. Manual time adjustments lacking segments count on today's
# date, and a negative correction reduces the most recent credited date first.
sub session_theory_seconds_by_local_date {
    my %days;
    for my $segment (session_segments_snapshot()) {
        next unless ($segment->{key} // '') eq 'y';
        my $seconds = $segment->{seconds} // 0;
        next unless $seconds > 0;
        my $from = $segment->{start_epoch} // 0;
        my $to = $segment->{end_epoch} // $from;
        next unless $from > 0 && $to > $from;
        my $duration = $to - $from;
        my $cursor = $from;
        while ($cursor < $to) {
            my @lt = localtime($cursor);
            my $date = strftime('%Y-%m-%d', @lt);
            my $local_noon = timelocal(0, 0, 12, $lt[3], $lt[4], $lt[5]);
            my @next_day = localtime($local_noon + 86400);
            my $next_midnight = timelocal(0, 0, 0,
                $next_day[3], $next_day[4], $next_day[5]);
            my $edge = $next_midnight < $to ? $next_midnight : $to;
            last if $edge <= $cursor;
            $days{$date} += $seconds * ($edge - $cursor) / $duration;
            $cursor = $edge;
        }
    }

    my $difference = theory_total();
    $difference -= $_ for values %days;
    if ($difference > 0.01) {
        $days{current_practice_day()} += $difference;
    }
    elsif ($difference < -0.01) {
        for my $date (reverse sort keys %days) {
            my $remove = -$difference < $days{$date} ? -$difference : $days{$date};
            $days{$date} -= $remove;
            $difference += $remove;
            last if $difference >= -0.01;
        }
    }
    return \%days;
}

# Each historical session's latest snapshot is authoritative. New snapshots
# record an exact per-date Theory breakdown. Legacy snapshots lack this field,
# so their positive deltas are assigned to each snapshot's local save date.
# Skip the live session's saved rows to avoid double-counting them.
sub theory_seconds_today {
    my $today = current_practice_day();
    my %sessions;
    my $sequence = 0;
    if (-e $LOG_FILE && open my $fh, '<', $LOG_FILE) {
        my $header = <$fh>;
        while (my $line = <$fh>) {
            chomp $line;
            $line =~ s/\r\z//;
            next if $line =~ /^\s*$/;
            my @cols = split /\t/, $line, -1;
            my $start = $cols[0] // '';
            my ($start_epoch) = parse_log_stamp($start);
            next unless defined($start_epoch);
            next if $start eq ($session_start_stamp // '');
            push @{ $sessions{$start} }, { cols => \@cols, index => $sequence++ };
        }
        close $fh;
    }

    my @opts = practice_options();
    my ($theory_index) = grep { $opts[$_]->{key} eq 'y' } 0 .. $#opts;
    my $today_total = 0;
    for my $start (keys %sessions) {
        my @snapshots = sort {
            ($a->{cols}->[1] // '') cmp ($b->{cols}->[1] // '')
                || $a->{index} <=> $b->{index}
        } @{ $sessions{$start} };
        my $latest = $snapshots[-1]{cols};
        my ($daily_field) = grep { /^daily_theory_dates=/ } @$latest;
        if (defined $daily_field) {
            my $by_date = decode_theory_calendar_days($daily_field);
            $today_total += $by_date->{$today} // 0 if defined $by_date;
            next;
        }

        # Pre-upgrade rows have no exact day-by-day category timeline.
        my %by_date;
        my $previous = 0;
        for my $row (@snapshots) {
            my $parsed = parse_activity_log_row_for_report($row->{cols}, \@opts);
            next unless defined $parsed;
            my $cumulative = $parsed->{category_seconds}->[$theory_index] // 0;
            my $delta = $cumulative - $previous;
            my $date = $previous == 0 && !keys(%by_date)
                ? date_from_stamp_text($start)
                : date_from_stamp_text($row->{cols}->[1] // '');
            $date //= date_from_stamp_text($start);
            if (defined $date && $delta > 0) {
                $by_date{$date} += $delta;
            }
            elsif ($delta < 0) {
                my $remaining = -$delta;
                for my $day (reverse sort keys %by_date) {
                    my $remove = $remaining < $by_date{$day} ? $remaining : $by_date{$day};
                    $by_date{$day} -= $remove;
                    $remaining -= $remove;
                    last if $remaining <= 0;
                }
            }
            $previous = $cumulative;
        }
        $today_total += $by_date{$today} // 0;
    }
    my $current_by_day = session_theory_seconds_by_local_date();
    $today_total += $current_by_day->{$today} // 0;
    return $today_total > 0 ? $today_total : 0;
}

sub decode_theory_calendar_days {
    my ($value) = @_;
    return undef unless defined($value) && $value =~ /\Adaily_theory_dates=(.*)\z/;
    my $contents = $1;
    my %days;
    return \%days if $contents eq '';
    for my $piece (split /,/, $contents) {
        return undef unless $piece =~ /\A(\d{4}-\d{2}-\d{2}):(\d+(?:\.\d+)?)\z/;
        $days{$1} += $2;
    }
    return \%days;
}

sub encode_theory_calendar_days {
    my ($days) = @_;
    return 'daily_theory_dates=' . join(',', map {
        $_ . ':' . sprintf('%.6f', $days->{$_})
    } sort keys %$days);
}

sub theory_daily_status {
    my ($seconds) = @_;
    return 'LOW' if $seconds < $THEORY_DAILY_MIN_SECONDS;
    return 'HIGH' if $seconds > $THEORY_DAILY_MAX_SECONDS;
    return 'OK';
}

# Optional last TSV column. This is session-cumulative, just like every other
# column, so the most recent save supersedes earlier saves for this session.
sub encode_practice_calendar_days {
    my ($days) = @_;
    return 'daily_active_dates=' . join(',', map {
        $_ . ':' . sprintf('%.6f', $days->{$_})
    } sort grep { ($days->{$_} // 0) > 0.001 } keys %$days);
}

sub decode_practice_calendar_days {
    my ($value) = @_;
    return undef unless defined($value) && $value =~ /\Adaily_active_dates=(.*)\z/;
    my $contents = $1;
    my %days;
    return \%days if $contents eq '';
    for my $piece (split /,/, $contents) {
        return undef unless $piece =~ /\A(\d{4}-\d{2}-\d{2}):(\d+(?:\.\d+)?)\z/;
        $days{$1} += $2;
    }
    return \%days;
}

# Pre-upgrade TSV rows did not record the day-by-day breakdown. Reconstruct
# their practice dates from successive cumulative saves, assigning each NEW
# increment to its save's local date. The first save is credited to the start
# date; negative corrections retract the latest credited practice first.
# This is the best available historical approximation; new rows are exact.
sub practice_calendar_totals_from_snapshots {
    my ($rows) = @_;
    my %sessions;
    my $sequence = 0;
    for my $cols (@$rows) {
        my $start = $cols->[0] // '';
        next unless statistics_include_date($start);
        my ($start_epoch) = parse_log_stamp($start);
        next unless defined $start_epoch;
        push @{$sessions{$start}}, { cols => $cols, index => $sequence++ };
    }

    my %all_days;
    my @options_for_log = practice_options();
    for my $start (keys %sessions) {
        my @snapshots = sort {
            ($a->{cols}->[1] // '') cmp ($b->{cols}->[1] // '')
                || $a->{index} <=> $b->{index}
        } @{$sessions{$start}};
        my $latest = $snapshots[-1]{cols};
        my ($active_dates_field) = grep { /^daily_active_dates=/ } @$latest;
        my $exact = decode_practice_calendar_days($active_dates_field);
        if (defined $exact) {
            for my $date (keys %$exact) {
                $all_days{$date} += $exact->{$date}
                    if statistics_include_date($date);
            }
            next;
        }

        my %by_day;
        my $previous = 0;
        for my $snapshot (@snapshots) {
            my $cols = $snapshot->{cols};
            my $parsed = parse_activity_log_row_for_report($cols, \@options_for_log);
            next unless $parsed;
            my $total = ($parsed->{active_seconds} // 0)
                + ($parsed->{scales_seconds} // 0)
                + ($parsed->{ear_training_seconds} // 0);
            my $delta = $total - $previous;
            my $date = $previous == 0 && !keys(%by_day)
                ? date_from_stamp_text($start)
                : date_from_stamp_text($cols->[1] // '');
            $date //= date_from_stamp_text($start);
            if ($delta > 0) {
                $by_day{$date} += $delta;
            }
            elsif ($delta < 0) {
                my $remaining = -$delta;
                for my $day (reverse sort keys %by_day) {
                    my $remove = $remaining < $by_day{$day} ? $remaining : $by_day{$day};
                    $by_day{$day} -= $remove;
                    $remaining -= $remove;
                    last if $remaining <= 0;
                }
            }
            $previous = $total;
        }
        for my $date (keys %by_day) {
            $all_days{$date} += $by_day{$date}
                if statistics_include_date($date);
        }
    }
    return \%all_days;
}

# Undo the latest recorded practice block, not the entire session.
# When a timer was left running accidentally, reclassify that block as
# Pause rather than shortening the session clock. Consecutive segments
# belonging to the same category/song are treated as one block; menus
# and reloads can split a single selection into multiple such segments.
# Reconstruct the latest completed selection that cleared the threshold.
# Segment boundaries caused by a menu or /r are not fresh song selections.
sub latest_qualified_song_epoch {
    my ($wanted) = @_;
    my ($latest, $group_seconds, $group_end) = (0, 0, 0);
    my ($group_id, $group_key, $group_selection) = ('', '', -1);
    for my $segment (@session_segments, { song_id => '', key => '' }) {
        my $id = $segment->{song_id} // '';
        my $key = $segment->{key} // '';
        my $selection = $segment->{selection_id} // 0;
        if ($id eq $wanted) {
            if ($group_id eq $id && $group_key eq $key
                && $group_selection == $selection) {
                $group_seconds += $segment->{seconds} // 0;
                $group_end = $segment->{end_epoch} // $group_end;
                next;
            }
        }
        elsif ($key eq pause_key() && $group_id eq $wanted
            && $group_selection > 0) {
            # A selection resumed after Pause remains one selection, even
            # though Pause's timeline segment carries no song ID.
            next;
        }
        $latest = $group_end
            if $group_seconds >= $MIN_SONG_SELECTION_SECONDS
                && $group_end > $latest;
        ($group_id, $group_key, $group_selection) =
            $id eq $wanted ? ($id, $key, $selection) : ('', '', -1);
        $group_seconds = $id eq $wanted ? ($segment->{seconds} // 0) : 0;
        $group_end = $id eq $wanted ? ($segment->{end_epoch} // 0) : 0;
    }
    return $latest;
}

sub undo_latest_practice {
    if ($undo_locked) {
        $last_message = 'Undo already used. Select a new practice category or song to enable it again.';
        return;
    }

    my $i = $#session_segments;
    while ($i >= 0) {
        my $segment = $session_segments[$i];
        my $key = $segment->{key} // '';
        last if ($segment->{seconds} // 0) > 0.001
            && exists $by_key{$key}
            && !$by_key{$key}->{is_pause}
            && !$by_key{$key}->{is_adjust};
        $i--;
    }
    if ($i < 0) {
        $last_message = 'Nothing to undo: no recorded practice block was found in this session.';
        return;
    }

    my $last = $session_segments[$i];
    my $category = $last->{key};
    my $song_id = $last->{song_id} // '';
    my $song_title = $last->{song_title} // '';
    my @block_indices = ($i);
    my $seconds = $last->{seconds};
    my $selection_id = $last->{selection_id} // 0;

    # Menu/reload splits are adjacent. Pause/Resume also keeps the SAME
    # selection ID, but inserts Pause segments between practice segments.
    # Undo must remove that complete selection without transferring Pause
    # segments a second time or incorrectly removing only part of a song's
    # credited time and its one selection count. Only bridge Pause when a
    # positive selection ID proves these pieces belong together.
    for (my $cursor = $i - 1; $cursor >= 0; $cursor--) {
        my $prior = $session_segments[$cursor];
        if (($prior->{key} // '') eq $category
            && ($prior->{song_id} // '') eq $song_id
            && ($prior->{selection_id} // 0) == $selection_id) {
            unshift @block_indices, $cursor;
            $seconds += $prior->{seconds};
        }
        elsif ($selection_id > 0 && length($song_id)
            && ($prior->{key} // '') eq pause_key()
            && ($prior->{song_id} // '') eq '') {
            next; # Already counted as Pause; leave it unchanged.
        }
        else {
            last;
        }
    }
    my $first = $block_indices[0];
    my $from = $session_segments[$first]->{start_epoch};
    my $to = $last->{end_epoch};

    # A prior manual correction may have already reduced the totals. Never
    # silently transfer more practice time than is actually present.
    my $song_was_credited = length($song_id)
        && $seconds >= $MIN_SONG_SELECTION_SECONDS;
    if (($elapsed{$category} // 0) + 0.01 < $seconds
        || ($song_was_credited && ($song_elapsed{$song_id} // 0) + 0.01 < $seconds)) {
        $last_message = 'Undo not safe: this block exceeds the remaining category/song total. Use Adjust instead.';
        return;
    }

    clear_screen();
    print "UNDO LAST PRACTICE BLOCK\n";
    print "========================\n\n";
    print "Category: [$category] $by_key{$category}->{name}\n";
    print "Song:     $song_title\n" if length $song_id;
    print 'From:     ' . fmt_stamp($from) . "\n";
    print 'Through:  ' . fmt_stamp($to) . "\n";
    print 'Duration: ' . fmt_time($seconds) . "\n\n";
    print "Move this practice time to Pause? [y/N] ";
    my $answer = ReadKey(0);
    print "\n";
    if (!defined($answer) || lc($answer) ne 'y') {
        $last_message = 'Undo canceled. Practice totals were not changed.';
        return;
    }

    # Correct category totals and retain the time as Pause. The separate
    # elapsed session clock is intentionally unchanged.
    $elapsed{$category} -= $seconds;
    $elapsed{$category} = 0 if $elapsed{$category} < 0.01;
    $elapsed{pause_key()} += $seconds;

    for my $idx (@block_indices) {
        my $segment = $session_segments[$idx];
        $segment->{key} = pause_key();
        $segment->{song_id} = '';
        $segment->{song_title} = '';
        $segment->{selection_id} = 0;
    }

    if ($song_was_credited) {
        $song_elapsed{$song_id} -= $seconds;
        $song_elapsed{$song_id} = 0 if $song_elapsed{$song_id} < 0.01;
        if (($song_practice_starts{$song_id} // 0) > 0) {
            $song_practice_starts{$song_id}--;
        }
        # Restore the timestamp of the latest *qualifying selection*.
        # A single selection can span multiple saved timeline segments.
        if ($song_elapsed{$song_id} == 0) {
            $song_last_practiced_epoch{$song_id} = 0;
        }
        else {
            my $previous_last = latest_qualified_song_epoch($song_id);
            $song_last_practiced_epoch{$song_id} = $previous_last
                if $previous_last > 0;
            # Manual song adjustments may have no segment: preserve their date.
        }
    }

    # If the erroneous category is still selected, stop it immediately.
    # Don't alter an unrelated active selection if undo was used after
    # switching categories; the latest completed block was corrected.
    if ($current_key eq $category && $current_song_id eq $song_id
        && $current_selection_id == $selection_id) {
        $current_key = pause_key();
        clear_current_song();
    }
    if (length($resume_key) && $resume_key eq $category
        && $resume_song_id eq $song_id
        && $resume_selection_id == $selection_id) {
        clear_resume_selection();
    }
    $undo_locked = 1;
    my $audit_note = audit_write({ action => 'PRACTICE_BLOCK_UNDONE',
        id => length($song_id) ? $song_id : "\@$category",
        old => fmt_time($seconds), new => 'Pause',
        detail => "Session $session_start_stamp; category $category; $song_title" });
    $last_message = 'Undid ' . fmt_time($seconds) . " of [$category] "
        . $by_key{$category}->{name} . '; moved it to Pause.' . $audit_note;
}

sub encode_session_segment {
    my ($segment) = @_;
    return join("\t",
        sprintf('%.6f', $segment->{start_epoch}),
        sprintf('%.6f', $segment->{end_epoch}),
        $segment->{key},
        unpack('H*', $segment->{song_id} // ''),
        unpack('H*', $segment->{song_title} // ''),
        sprintf('%.6f', $segment->{seconds}),
        ($segment->{selection_id} // 0),
    );
}

sub decode_session_segment {
    my ($value) = @_;
    return undef unless defined $value;
    my @fields = split /\t/, $value, -1;
    return undef unless @fields == 6 || @fields == 7;
    my ($start, $end, $key, $id_hex, $title_hex, $duration, $selection_id) = @fields;
    $selection_id //= 0; # Backward-compatible with old timeline records.
    return undef unless $selection_id =~ /^\d+$/;
    $key = 's' if $key eq 't';  # Pre-rename timeline segments.
    return undef unless $start =~ /^\d+(?:\.\d+)?$/
        && $end =~ /^\d+(?:\.\d+)?$/
        && $duration =~ /^\d+(?:\.\d+)?$/;
    return undef unless exists $by_key{$key} && !$by_key{$key}->{is_adjust};
    return undef unless $id_hex =~ /^(?:[0-9a-f]{2})*$/
        && $title_hex =~ /^(?:[0-9a-f]{2})*$/;
    return undef if $end < $start;
    return {
        start_epoch => 0 + $start,
        end_epoch => 0 + $end,
        key => $key,
        song_id => pack('H*', $id_hex),
        song_title => pack('H*', $title_hex),
        seconds => 0 + $duration,
        selection_id => 0 + $selection_id,
    };
}

# Legacy state files (prior to the per-selection minimum) already included
# seconds and starts for very short selections. Use their chronological blocks
# to remove those provisional selections when the user reloads an old session.
# Preserve explicit manual additions, which have no corresponding timeline
# block, and preserve unknown older history when no timeline is available.
sub upgrade_legacy_song_selections {
    my @blocks;
    for my $i (0 .. $#session_segments) {
        my $segment = $session_segments[$i];
        my $id = $segment->{song_id} // '';
        next unless length($id) && ($segment->{seconds} // 0) > 0;
        my $key = $segment->{key} // '';
        if (@blocks && $blocks[-1]{id} eq $id
            && $blocks[-1]{key} eq $key
            && $blocks[-1]{last_index} == $i - 1) {
            $blocks[-1]{seconds} += $segment->{seconds};
            $blocks[-1]{last_index} = $i;
        }
        else {
            push @blocks, {
                id => $id, key => $key, seconds => $segment->{seconds},
                first_index => $i, last_index => $i,
            };
        }
    }
    my (%discarded_seconds, %discarded_starts);
    for my $block (@blocks) {
        next if $block->{seconds} >= $MIN_SONG_SELECTION_SECONDS;
        $discarded_seconds{$block->{id}} += $block->{seconds};
        $discarded_starts{$block->{id}}++;
    }
    for my $id (keys %discarded_seconds) {
        next unless exists $song_elapsed{$id};
        $song_elapsed{$id} -= $discarded_seconds{$id};
        $song_elapsed{$id} = 0 if $song_elapsed{$id} < 0.01;
        $song_practice_starts{$id} -= $discarded_starts{$id};
        $song_practice_starts{$id} = 0 if $song_practice_starts{$id} < 0;
        $song_last_practiced_epoch{$id} = 0 if $song_elapsed{$id} == 0;
    }

    # The last (possibly partial) selection stays active across /r.
    # Assign it an ID so further segments belong to the same selection.
    $selection_serial = 0;
    $current_selection_id = 0;
    $current_selection_seconds = 0;
    $current_selection_qualified = 0;
    return unless length $current_song_id;
    return unless @blocks;
    my $last = $blocks[-1];
    return unless $last->{id} eq $current_song_id
        && $last->{key} eq $current_key
        && $last->{last_index} == $#session_segments;
    $current_selection_seconds = $last->{seconds};
    $current_selection_qualified =
        $current_selection_seconds >= $MIN_SONG_SELECTION_SECONDS ? 1 : 0;
    $current_selection_id = ++$selection_serial;
    for my $i ($last->{first_index} .. $last->{last_index}) {
        $session_segments[$i]{selection_id} = $current_selection_id;
    }
}

sub save_state {
    persist_last_practice_epoch(1);
    my $file = $STATE_FILE;
    my $saved_at_epoch = time;

    open my $fh, '>', $file
        or die "Could not write to $file: $!";

    print $fh "version=4\n";
    printf $fh "saved_at_epoch=%.6f\n", $saved_at_epoch;
    print $fh "saved_at_stamp=" . fmt_stamp($saved_at_epoch) . "\n";
    printf $fh "session_start_epoch=%.6f\n", $session_start;
    print $fh "session_start_stamp=$session_start_stamp\n";
    printf $fh "session_elapsed_seconds=%.6f\n", session_elapsed();
    print $fh "current_key=$current_key\n";
    # Backward-compatible extension to the existing session state format.
    print $fh "resume_key=$resume_key\n";
    print $fh "resume_song_id=$resume_song_id\n";
    print $fh "resume_song_title=$resume_song_title\n";
    printf $fh "resume_selection_seconds=%.6f\n", $resume_selection_seconds;
    print $fh "resume_selection_qualified=$resume_selection_qualified\n";
    print $fh "resume_selection_id=$resume_selection_id\n";
    print $fh "current_song_id=$current_song_id\n";
    print $fh "current_song_title=$current_song_title\n";
    printf $fh "current_selection_seconds=%.6f\n", $current_selection_seconds;
    print $fh "current_selection_qualified=$current_selection_qualified\n";
    print $fh "current_selection_id=$current_selection_id\n";
    print $fh "current_was_unpaused=$current_was_unpaused\n";
    printf $fh "current_since_unpaused_seconds=%.6f\n", $current_since_unpaused_seconds;
    print $fh "selection_serial=$selection_serial\n";
    print $fh "undo_locked=$undo_locked\n";

    print $fh "session_timeline_version=1\n";
    print $fh "session_timeline_partial=$session_timeline_partial\n";
    my @segments = session_segments_snapshot();
    print $fh "session_segment_count=" . scalar(@segments) . "\n";
    for my $i (0 .. $#segments) {
        print $fh "session_segment_$i=" . encode_session_segment($segments[$i]) . "\n";
    }

    for my $song_id (sort keys %song_elapsed) {
        # Hex-encode only the state key, not the ID itself; this preserves
        # arbitrary IDs in the TSV while keeping the state file unambiguous.
        my $state_id = unpack('H*', $song_id);
        printf $fh "song_elapsed_hex_%s=%.6f\n", $state_id, $song_elapsed{$song_id};
        print $fh "song_title_hex_$state_id=" . ($song_titles{$song_id} // '') . "\n";
        printf $fh "song_starts_hex_%s=%d\n", $state_id, ($song_practice_starts{$song_id} // 0);
        printf $fh "song_last_epoch_hex_%s=%.6f\n", $state_id, ($song_last_practiced_epoch{$song_id} // 0);
    }

    for my $option (@options) {
        my $key = $option->{key};
        printf $fh "elapsed_%s=%.6f\n", $key, $elapsed{$key};
    }

    close $fh;
}

sub load_state {
    my $file = $STATE_FILE;

    return (0, "No saved session file found: $file")
        unless -e $file;

    open my $fh, '<', $file
        or return (0, "Could not read $file: $!");

    my %state;

    while (my $line = <$fh>) {
        chomp $line;
        next if $line =~ /^\s*$/;
        next if $line =~ /^\s*#/;

        my ($key, $value) = split /=/, $line, 2;
        next unless defined $key;
        $value //= '';
        $state{$key} = $value;
    }

    close $fh;

    my $saved_session_start = number_or_zero($state{session_start_epoch});
    return (0, "Saved session is missing a valid session_start_epoch.")
        if $saved_session_start <= 0;

    $session_start       = $saved_session_start;
    $session_start_stamp = $state{session_start_stamp} || fmt_stamp($session_start);

    $session_elapsed_offset = number_or_zero($state{session_elapsed_seconds});
    $session_elapsed_offset = 0 if $session_elapsed_offset < 0;
    $session_clock_anchor   = time;
    $undo_locked = number_or_zero($state{undo_locked}) > 0 ? 1 : 0;

    # Backward compatibility: in older saved sessions, elapsed_6 meant Pause.
    # In the current version, key 6 is Cold Storage and Pause is p.
    # If a state file has elapsed_6 but not elapsed_p, treat elapsed_6 as legacy
    # Pause data and do not also load it into Cold Storage.
    my $legacy_pause_elapsed_6 = (!exists $state{elapsed_p} && exists $state{elapsed_6});

    for my $option (@options) {
        my $key = $option->{key};
        my $state_key = "elapsed_$key";

        # Existing sessions tracked Scales under the former key t.
        # Import it once; new state files will write elapsed_s instead.
        if ($key eq 's' && !exists $state{elapsed_s} && exists $state{elapsed_t}) {
            $state_key = 'elapsed_t';
        }

        if ($key eq '6' && $legacy_pause_elapsed_6) {
            $state_key = undef;
        }

        # Backward compatibility: older saved sessions used key 6 for Pause.
        # Pause is now key p, but old elapsed_6 data should still reload as Pause.
        if ($option->{is_pause}
            && !exists $state{$state_key}
            && exists $state{elapsed_6}) {
            $state_key = 'elapsed_6';
        }

        # Backward compatibility: older saved sessions used key 7 for Adjust.
        # Adjust is now key a. Adjust is not normally timed, but preserving this
        # keeps the state reader tolerant of older files.
        if ($option->{is_adjust}
            && !exists $state{$state_key}
            && exists $state{elapsed_7}) {
            $state_key = 'elapsed_7';
        }

        my $value = defined $state_key ? number_or_zero($state{$state_key}) : 0;
        $elapsed{$key} = $value < 0 ? 0 : $value;
    }

    my $saved_current_key = $state{current_key};
    $saved_current_key = 's'
        if defined $saved_current_key && $saved_current_key eq 't';

    # Backward compatibility for sessions saved when key 6 meant Pause.
    $saved_current_key = pause_key()
        if defined $saved_current_key
            && $saved_current_key eq '6'
            && $legacy_pause_elapsed_6;

    # Adjust is a command, not a timer category. If an older file somehow saved
    # Adjust as the current key, return safely to Pause on reload.
    $saved_current_key = pause_key()
        if defined $saved_current_key && $saved_current_key eq '7';

    if (defined $saved_current_key
        && exists $by_key{$saved_current_key}
        && !$by_key{$saved_current_key}->{is_adjust}
        && !$by_key{$saved_current_key}->{is_retired}) {
        $current_key = $saved_current_key;
    }
    else {
        $current_key = pause_key();
    }

    # Older state files have no per-song information and still reload normally.
    %song_elapsed = ();
    %song_titles = ();
    %song_practice_starts = ();
    %song_last_practiced_epoch = ();
    for my $state_key (keys %state) {
        # Accept the encoded handle keys from this version, as well as any
        # plain keys from transitional states.
        my ($song_id, $suffix);
        if ($state_key =~ /^song_elapsed_hex_([0-9a-f]+)$/ && length($1) % 2 == 0) {
            $song_id = pack('H*', $1);
            $suffix = "hex_$1";
        }
        elsif ($state_key =~ /^song_elapsed_([a-z0-9_]+)$/) {
            $song_id = $1;
            $suffix = $song_id;
        }
        else {
            next;
        }
        my $seconds = number_or_zero($state{$state_key});
        $song_elapsed{$song_id} = $seconds < 0 ? 0 : $seconds;
        $song_titles{$song_id} = $state{"song_title_$suffix"} // $song_id;
        $song_practice_starts{$song_id} = int(number_or_zero($state{"song_starts_$suffix"}));
        $song_last_practiced_epoch{$song_id} = number_or_zero($state{"song_last_epoch_$suffix"});
    }

    $current_song_id = $state{current_song_id} // '';
    $current_song_title = $state{current_song_title} // '';
    if (!length $current_song_id
        || !exists $by_key{$current_key}
        || $by_key{$current_key}->{is_pause}
        || is_supplemental_key($current_key)
        || $by_key{$current_key}->{is_adjust}) {
        clear_current_song();
    }
    else {
        $current_song_title ||= $song_titles{$current_song_id} // $current_song_id;
        # A new provisional selection may have no credited song_elapsed row
        # yet; its title must still survive /r for the eventual log entry.
        $song_titles{$current_song_id} = $current_song_title;
    }

    # State versions before this feature did not record the order of practice.
    # Preserve their accumulated totals without inventing a timeline.
    @session_segments = ();
    $active_segment = undef;
    $session_timeline_partial = !exists($state{session_timeline_version})
        || number_or_zero($state{session_timeline_partial}) ? 1 : 0;
    if (exists $state{session_timeline_version}) {
        my $count = int(number_or_zero($state{session_segment_count}));
        $count = 0 if $count < 0;
        $count = 100000 if $count > 100000;
        for my $i (0 .. $count - 1) {
            my $segment = decode_session_segment($state{"session_segment_$i"});
            if ($segment) {
                push @session_segments, $segment;
            }
            else {
                $session_timeline_partial = 1;
            }
        }
    }

    # Upgrade an old saved session that credited every accidental song
    # selection immediately. The existing timeline lets us remove short
    # blocks without erasing manually adjusted song time.
    if (!exists $state{current_selection_seconds}) {
        upgrade_legacy_song_selections();
    }
    else {
        $current_selection_seconds = number_or_zero($state{current_selection_seconds});
        $current_selection_qualified = number_or_zero($state{current_selection_qualified}) ? 1 : 0;
        $current_selection_id = int(number_or_zero($state{current_selection_id}));
        $selection_serial = int(number_or_zero($state{selection_serial}));
        $current_selection_seconds = 0 if $current_selection_seconds < 0;
        $selection_serial = $current_selection_id
            if $current_selection_id > $selection_serial;
    }
    clear_current_song() unless length $current_song_id;
    # Old state files load normally, with no parenthesized timer until an
    # actual pause/resume. Saved resumed stretches survive /r unchanged.
    if (length $current_song_id) {
        $current_was_unpaused = number_or_zero($state{current_was_unpaused}) ? 1 : 0;
        $current_since_unpaused_seconds = $current_was_unpaused
            ? number_or_zero($state{current_since_unpaused_seconds}) : 0;
        $current_since_unpaused_seconds = 0 if $current_since_unpaused_seconds < 0;
    }

    # A legacy state has none of these fields and remains simply paused.
    # Restore the suspended selection only when the saved timer was paused;
    # never revive a stale selection while another category is running.
    clear_resume_selection();
    if ($current_key eq pause_key()) {
        my $key = $state{resume_key} // '';
        $key = 's' if $key eq 't';
        if (exists $by_key{$key}
            && !$by_key{$key}->{is_pause} && !$by_key{$key}->{is_adjust}
            && !$by_key{$key}->{is_retired}) {
            $resume_key = $key;
            $resume_song_id = $state{resume_song_id} // '';
            $resume_song_title = $state{resume_song_title} // '';
            $resume_selection_seconds = number_or_zero($state{resume_selection_seconds});
            $resume_selection_seconds = 0 if $resume_selection_seconds < 0;
            $resume_selection_qualified = number_or_zero($state{resume_selection_qualified}) ? 1 : 0;
            $resume_selection_id = int(number_or_zero($state{resume_selection_id}));
            if (length $resume_song_id) {
                # Only song-bearing categories can have a suspended song.
                if (is_supplemental_key($key)) {
                    $resume_song_id = '';
                    $resume_song_title = '';
                    $resume_selection_seconds = 0;
                    $resume_selection_qualified = 0;
                    $resume_selection_id = 0;
                }
                else {
                    $resume_song_title ||= $song_titles{$resume_song_id} // $resume_song_id;
                    $song_titles{$resume_song_id} = $resume_song_title;
                }
            }
            if ($resume_selection_id > $selection_serial) {
                $selection_serial = $resume_selection_id;
            }
        }
    }

    $last_tick = time;

    my $saved_at = $state{saved_at_stamp} || 'unknown time';
    return (1, "Reloaded saved session from $saved_at.");
}

sub init_new_session {
    my ($start_input) = @_;

    %elapsed = map { $_->{key} => 0 } @options;
    %song_elapsed = ();
    %song_titles = ();
    %song_practice_starts = ();
    %song_last_practiced_epoch = ();
    $current_selection_seconds = 0;
    $current_selection_qualified = 0;
    $current_selection_id = 0;
    $selection_serial = 0;
    @session_segments = ();
    $active_segment = undef;
    $session_timeline_partial = 0;
    $undo_locked = 0;
    clear_current_song();
    clear_resume_selection();
    $current_key = pause_key();

    $session_start       = initial_session_start($start_input);
    $session_start_stamp = fmt_stamp($session_start);

    # A manually supplied start time should produce the corresponding displayed session elapsed.
    $session_elapsed_offset = time - $session_start;
    $session_elapsed_offset = 0 if $session_elapsed_offset < 0;
    $session_clock_anchor = time;
    $last_tick            = time;
}

# /n protection: an accidentally repeated /n should not replace a session
# which has been started but contains only Pause/idle time. This deliberately
# inspects saved state without loading or changing the previous session.
sub confirm_new_session_if_no_practice {
    return 1 unless -f $STATE_FILE;

    open my $fh, '<', $STATE_FILE
        or die "Cannot inspect saved session $STATE_FILE: $!\n";

    my %elapsed_saved;
    while (my $line = <$fh>) {
        chomp $line;
        if ($line =~ /^elapsed_([^=]+)=([+-]?(?:\d+(?:\.\d*)?|\.\d+))\s*$/) {
            $elapsed_saved{$1} = 0 + $2;
        }
    }
    close $fh;

    # The old state layout used elapsed_6 for Pause. New state files
    # explicitly contain elapsed_p, and 6 then means Cold Storage.
    my $old_pause_key_6 = !exists $elapsed_saved{p};
    for my $key (keys %elapsed_saved) {
        next if $key eq 'p' || $key eq 'a' || $key eq '7';
        next if $key eq '6' && $old_pause_key_6;
        return 1 if $elapsed_saved{$key} >= 1; # >= 1 second of actual practice
    }

    print "\nWARNING: The saved session has no recorded practice.\n";
    print "Starting with /n will replace it and begin a new practice day.\n";
    print "Are you REALLY sure you want to start a new session? [y/N] ";
    my $answer = <STDIN>;
    return defined($answer) && $answer =~ /^\s*y(?:es)?\s*$/i;
}

sub start_from_command_line {
    my ($mode, $start_input) = @_;

    if ($mode eq 'reload') {
        my ($ok, $msg) = load_state();

        if (!$ok) {
            die "$msg\n";
        }

        $last_message = $msg;
        return;
    }

    if ($mode eq 'new') {
        if (!confirm_new_session_if_no_practice()) {
            print "New session cancelled. Use /r to resume your saved session.\n";
            exit 0;
        }
        init_new_session($start_input);
        $last_message = "Started a new session.";
        return;
    }

    die usage();
}


# Manage delayed tips without coupling them to song timing or session state.
# The PracticeTips module owns persistence, parsing, ordering, and time shifts.
sub manage_custom_tips {
    ReadMode('restore');
    my $notice = '';
    while (1) {
        clear_screen();
        print "CUSTOM TIPS / REMINDERS\n";
        print "=======================\n\n";
        my ($items, $error) = PracticeTips::list_custom_tips($SONG_CATEGORY_FILE);
        if ($error) {
            $notice = $error;
            print "$error\n";
            last;
        }
        my $now = time;
        if (@$items) {
            for my $index (0 .. $#$items) {
                my $item = $items->[$index];
                my $due = strftime('%Y-%m-%d %I:%M %p', localtime($item->{due}));
                my $status = $item->{due} <= $now ? 'DUE' : 'scheduled';
                printf " %2d. [%s] %s - %s\n", $index + 1,
                    $status, $due, $item->{text};
            }
        }
        else {
            print "No custom reminders.\n";
        }
        print "\n$notice\n" if length $notice;
        $notice = '';
        print "\n[a] Add   [t] Time +/-   [d] Delete   [Enter] Return: ";
        my $command = <STDIN>;
        last unless defined $command;
        $command =~ s/^\s+|\s+\z//g;
        last if $command eq '';
        if (lc($command) eq 'a') {
            print "Reminder (one line): ";
            my $message = <STDIN>;
            last unless defined $message;
            chomp $message;
            $message =~ s/\r\z//;
            if ($message !~ /\S/) {
                $notice = 'No reminder added (blank text).';
                next;
            }
            print "When? 1d5h, 2h, 30m, or YYYY-MM-DD HH:MM: ";
            my $when = <STDIN>;
            last unless defined $when;
            chomp $when;
            $when =~ s/\r\z//;
            my ($entry, $error) = PracticeTips::add_custom_tip(
                $SONG_CATEGORY_FILE, $message, $when);
            $notice = $error // 'Added reminder for '
                . strftime('%Y-%m-%d %I:%M %p', localtime($entry->{due})) . '.';
        }
        elsif (lc($command) eq 't') {
            if (!@$items) { $notice = 'No reminders to adjust.'; next; }
            print "Reminder number to adjust: ";
            my $number = <STDIN>;
            last unless defined $number;
            $number =~ s/^\s+|\s+\z//g;
            if ($number !~ /\A\d+\z/ || $number < 1 || $number > @$items) {
                $notice = 'Invalid reminder number.';
                next;
            }
            my $selected = $items->[$number - 1];
            my $old_due = strftime('%Y-%m-%d %I:%M %p', localtime($selected->{due}));
            print "Reminder: $selected->{text}\n";
            print "Currently scheduled: $old_due"
                . ($selected->{due} <= time ? ' [DUE]' : ' [scheduled]') . "\n";
            print "Add/subtract (+2d1h, -3h, +30m; 2d also adds): ";
            my $shift = <STDIN>;
            last unless defined $shift;
            $shift =~ s/^\s+|\s+\z//g;
            if ($shift eq '') { $notice = 'Time adjustment canceled.'; next; }
            my ($updated, $error) = PracticeTips::adjust_custom_tip_time(
                $SONG_CATEGORY_FILE, $selected->{id}, $shift);
            if ($error) { $notice = $error; }
            else {
                my $when = strftime('%Y-%m-%d %I:%M %p', localtime($updated->{due}));
                $notice = "Reminder moved to $when"
                    . ($updated->{due} <= time ? ' (DUE).' : ' (scheduled).');
            }
        }
        elsif (lc($command) eq 'd') {
            if (!@$items) { $notice = 'Nothing to delete.'; next; }
            print "Reminder number to delete: ";
            my $number = <STDIN>;
            last unless defined $number;
            $number =~ s/^\s+|\s+\z//g;
            if ($number !~ /\A\d+\z/ || $number < 1 || $number > @$items) {
                $notice = 'Invalid reminder number.';
                next;
            }
            my $selected = $items->[$number - 1];
            print "Delete reminder '$selected->{text}'? [y/N]: ";
            my $confirm = <STDIN>;
            last unless defined $confirm;
            if ($confirm =~ /^\s*y\s*$/i) {
                my ($ok, $error) = PracticeTips::delete_custom_tip(
                    $SONG_CATEGORY_FILE, $selected->{id});
                $notice = $error // 'Reminder deleted.';
            }
            else { $notice = 'Deletion canceled.'; }
        }
        else { $notice = 'Press a to add, t to adjust time, d to delete, or Enter to return.'; }
    }
    ReadMode('cbreak');
    $last_tick = time;  # Time spent in this menu is not practice time.
    return;
}

# Calculate credited song practice in the CURRENT /n practice day from
# the existing session timeline. A selection shorter than 60 seconds contributes nothing, just as
# it contributes nothing to the ordinary song statistics. This also handles
# sessions that span midnight or are resumed using /r; no extra state file is
# needed, and Undo immediately restores a song's tip eligibility.
sub today_qualified_song_seconds {
    my @segments = session_segments_snapshot();

    my %groups;
    my $legacy_group = 0;
    my ($previous_id, $previous_key) = ('', '');
    for my $seg (@segments) {
        my $id = $seg->{song_id} // '';
        my $selection = $seg->{selection_id} // 0;
        next unless length $id && ($seg->{seconds} // 0) > 0;
        my $group_key;
        if ($selection > 0) {
            $group_key = join("\0", $id, $selection);
        }
        else {
            # Backward compatibility for timeline segments saved before
            # individual selection IDs were introduced.
            if ($id ne $previous_id || ($seg->{key} // '') ne $previous_key) {
                $legacy_group++;
            }
            $group_key = join("\0", 'legacy', $legacy_group, $id);
        }
        push @{ $groups{$group_key}{segments} }, $seg;
        $groups{$group_key}{id} = $id;
        $groups{$group_key}{total} += $seg->{seconds};
        ($previous_id, $previous_key) = ($id, $seg->{key} // '');
    }

    my %today;
    for my $group (values %groups) {
        next if $group->{total} + 0.001 < $MIN_SONG_SELECTION_SECONDS;
        for my $seg (@{ $group->{segments} }) {
            $today{ $group->{id} } += $seg->{seconds} // 0;
        }
    }
    # Song totals are authoritative after manual reductions or Undo.
    for my $id (keys %today) {
        my $total = $song_elapsed{$id} // 0;
        $today{$id} = $total if $today{$id} > $total;
        delete $today{$id} if $today{$id} <= 0;
    }
    return \%today;
}

# Live main-screen rankings use the same individual practice-day ranks
# as practice_activity_report.txt. Read the master log using its LAST snapshot
# for each session start, but replace the current session's stored snapshot
# with its in-memory totals. This prevents double-counting after Save/View.
# Category-synced dated corrections count; song-only corrections do not.
# Calendar day splits at local midnight, even within an ongoing session.
sub live_practice_totals_by_date {
    my @snapshot_rows;
    if (-e $LOG_FILE && open my $fh, '<', $LOG_FILE) {
        my $header = <$fh>;
        while (my $line = <$fh>) {
            chomp $line;
            $line =~ s/\r\z//;
            next if $line =~ /^\s*$/;
            my @fields = split /\t/, $line, -1;
            # In-progress totals are authoritative, even if already saved.
            next if defined($session_start_stamp) && ($fields[0] // '') eq $session_start_stamp;
            push @snapshot_rows, \@fields;
        }
        close $fh;
    }
    my $totals = practice_calendar_totals_from_snapshots(\@snapshot_rows);

    my ($adjustments) = read_song_adjustment_log($SONG_ADJUST_FILE);
    for my $entry (@$adjustments) {
        next unless $entry->{sync} && statistics_include_date($entry->{date});
        $totals->{$entry->{date}} += $entry->{seconds};
    }
    if (statistics_include_date($session_start_stamp // '')) {
        my $current_days = session_active_seconds_by_local_date();
        for my $date (keys %$current_days) {
            $totals->{$date} += $current_days->{$date}
                if statistics_include_date($date);
        }
    }
    return $totals;
}

# Calendar and daily rankings follow Eastern-local dates on the user's PC,
# rather than a /n session that may last several consecutive calendar days.
sub current_practice_day {
    return strftime('%Y-%m-%d', localtime(time));
}

sub main_screen_percentiles {
    my ($today_ymd) = @_;
    $today_ymd //= current_practice_day();
    my $totals = live_practice_totals_by_date();
    my $stats = practice_percentile_stats($totals, $today_ymd);
    my $all = practice_percentile_display(
        $stats ? $stats->{daily_percentile} : undef,
        $stats ? $stats->{all_rank} : undef,
        $stats ? $stats->{all_count} : undef, 1, 'N/A');
    my $week = practice_rank_ordinal($stats ? $stats->{week_rank} : undef);
    my $fortnight = practice_rank_ordinal($stats ? $stats->{fortnight_rank} : undef);
    return "All: $all  7 Day: $week  14 Day: $fortnight";
}

# Keep percentile calculations on the ten-second full-screen cycle: they
# read historical TSVs and should not hit disk on every one-second clock tick.
sub main_screen_status_line {
    my ($fast) = @_;
    my $ranks = $fast && length($main_screen_cached_percentiles)
        ? $main_screen_cached_percentiles : main_screen_percentiles();
    $main_screen_cached_percentiles = $ranks unless $fast;
    return "Active practice:  " . fmt_time(reported_active_total()) . "  "
        . $ranks . "  Time since last practice: "
        . time_since_last_practice_label();
}

# These two timer lines are also used by the one-second refresh. Keep
# formatting in one place so partial updates exactly match full redraws.
sub main_screen_song_session_line {
    my $line = 'Song this session: ' . fmt_time($song_elapsed{$current_song_id} // 0);
    if ($current_was_unpaused && length($current_song_id)) {
        $line .= ' (since unpaused: ' . fmt_time($current_since_unpaused_seconds) . ')';
    }
    return $line;
}

sub main_screen_selection_pending_line {
    return 'Selection pending: ' . fmt_time($current_selection_seconds)
        . ' (counts after 1 minute)';
}

sub render {
    # The idle alert remains a deliberate five-second full-screen flash.
    maybe_flash_idle_practice_alert();

    # Capture all ordinary print/printf calls (also the PracticeTips module)
    # into a frame instead of sending partial output to the live console.
    my $frame = '';
    open my $memory, '>', \$frame or die "Cannot buffer main screen: $!";
    {
        local *STDOUT = $memory;
        render_main_screen_contents();
    }
    close $memory or die "Cannot finish buffered main screen: $!";
    present_main_screen($frame);
}

sub render_main_screen_contents {
    print "-------------------------------------------------------------------------------------------------\n";
    print main_screen_status_line(0), "\n";
    print "-------------------------------------------------------------------------------------------------\n";
    # A due memory check is an invitation to verify recall without tabs.
    # This is read-only and never alters song time, attributes, or tips.
    my ($memory_records) = read_song_categories_tsv($SONG_CATEGORY_FILE);
    if ($memory_records) {
        my ($memory_attributes, $attr_error) = read_song_attributes();
        if ($memory_attributes && !$attr_error) {
            my $due_count = memorized_review_due_count($memory_records, $memory_attributes);
            print "Memorized tests due: $due_count (F8 -> r to review)\n"
                if $due_count > 0;
        }
    }
    if (length $current_song_id) {
        my ($song_attrs) = read_song_attributes();
        my $marks = song_attribute_labels($song_attrs // {}, $current_song_id);
        $marks = " $marks" if length $marks;
        print "Current song:     $current_song_title [$current_song_id]$marks\n";
        print main_screen_song_session_line(), "\n";
        if (!$current_selection_qualified) {
            print main_screen_selection_pending_line(), "\n";
        }
    }
    elsif (is_media_activity_key($current_key)) {
        print 'Current selection: ' . $by_key{$current_key}->{name} . " (t = media menu)\n";
    }
    elsif ($current_key eq pause_key() && length $resume_key) {
        my $label = length($resume_song_title)
            ? $resume_song_title . " [$resume_song_id]"
            : $by_key{$resume_key}->{name};
        if (length $resume_song_id) {
            my ($song_attrs) = read_song_attributes();
            my $marks = song_attribute_labels($song_attrs // {}, $resume_song_id);
            $label .= " $marks" if length $marks;
        }
        print "Paused selection: [$resume_key] $label\n";
    }
    else {
        print "Current song:     (none; category-only timing)\n";
    }
    print "\n";

    printf "%-5s %-34s %12s %10s %12s %8s\n",
        "ID", "Option", "Elapsed", "%", "Target", "Status";

    print "-" x 89 . "\n";

    my $theory_today = theory_seconds_today();
    for my $option (@options) {
        next if $option->{is_adjust} || $option->{is_retired};
        # Retired Jamming remains in historical data, not on the main screen.

        my $key = $option->{key};
        my $marker = $key eq $current_key ? '>' : ' ';

        printf "%s %-3s %-34s %12s ",
            $marker,
            $key,
            $option->{name},
            fmt_time($key eq 'y' ? $theory_today : $elapsed{$key});

        if ($option->{is_scales} || $option->{is_ear_training}) {
            my $pct = supplemental_percent_for($key);
            printf "%9d%% %12s %8s\n",
                int($pct + 0.5),
                target_label($option),
                supplemental_status_for($option);
        }
        elsif ($key eq 'y') {
            printf "%10s %12s %8s\n", "-", target_label($option),
                theory_daily_status($theory_today);
        }
        elsif ($option->{is_pause} || $option->{is_adjust}) {
            printf "%10s %12s %8s\n", "-", target_label($option), "";
        }
        else {
            my $pct       = percent_for($key);
            my $pct_whole = int($pct + 0.5);

            printf "%9d%% %12s %8s\n",
                $pct_whole,
                target_label($option),
                status_for($option, $pct);
        }
    }

    print "-" x 89 . "\n";
    print "Theory shows today's total (local midnight to midnight); other Elapsed values are session totals.\n";

    print "\n$last_message\n" if length $last_message;
    print "\n$audit_alert\n" if length $audit_alert;
    # Disable the experimental tips by commenting out this one line.
    $displayed_tip_song_id = PracticeTips::show_tip(
        $SONG_CATEGORY_FILE, $LOG_FILE, $SONG_LOG_FILE,
        $SONG_ADJUST_FILE, $session_start_stamp, \%song_elapsed,
        today_qualified_song_seconds()) // '';
    # Quotes already contain their intended punctuation in quotes.txt.
    # Never add a second set of quotation marks around the entire entry.
    print "\n$CURRENT_QUOTE\n" if length $CURRENT_QUOTE;

    print "\n--------------------------------------------------------------------------------------------------------------------------\n";
    # Compact shortcut reference; keep the main timer on screen.
    # Parentheses show the physical US QWERTY key for a US Dvorak layout.
    # Uppercase shortcuts require Shift in addition to the indicated key.
    # Ear training uses h(j) because e(d) is already Edit MP3.
    print "F-KEY ROW:  F1 Pause/Resume | F2 Find | F3 Open media | F4 View | F5 New tip | F6 +1 Theory | F7 +1 Scales | F8 Attributes\n";
    print "            F9 Media menu | F10 Emphasize\n";
    print "NUMBER ROW: 1 Pause | 2 Find | 3 Open media | 4 View | 5 New tip | 6 Tip song | 7 Scales | 8 Ear | 9 Theory | 0 Reminders\n";
    print "Practice:   p(r) Pause/Resume | b(n)/F7 +1 Scales | F6 +1 Theory\n";
    print "Songs:      f(y)/P(Shift+r) Find | c(i) Categories | n(l) Add song | t(k) Media | e(d) Edit MP3\n";
    print "Tools:      a(a) Adjust | u(f) Undo | v(.) View | l(p) Activity report (gVim) | d(h) Descriptions | z(/) Repertoire guide\n";
    print "Session:    T(Shift+k) Change start time | S(Shift+;) Save | q(x)/x(b) Quit\n";

}

# Human-readable View for the CURRENT session. Rendering is read-only; the
# separately confirmed delete action can amend this session and its logs.
sub session_view_time {
    my ($epoch) = @_;
    my $text = strftime('%I:%M %p', localtime($epoch));
    $text =~ s/^0//;
    return $text;
}

sub session_view_bar {
    my ($percent, $width) = @_;
    $width ||= 14;
    $percent = 0 unless defined $percent && $percent > 0;
    my $filled = int(($percent / 100) * $width + 0.5);
    $filled = $width if $filled > $width;
    return ('#' x $filled) . ('.' x ($width - $filled));
}

sub session_view_wrap {
    my ($text, $width, $indent) = @_;
    $text //= '';
    $indent //= '';
    my @lines;
    while (length($text) > $width) {
        my $cut = rindex($text, ' ', $width);
        $cut = $width if $cut < int($width / 2);
        push @lines, substr($text, 0, $cut);
        $text = substr($text, $cut);
        $text =~ s/^\s+//;
    }
    push @lines, $text;
    return join("\n$indent", @lines);
}

# The numbered View list and the deletion chooser must share EXACTLY the
# same ordering, even when two songs have the same last-practiced time.
sub session_view_entries {
    my $scales = scales_total();
    my $ear_training = ear_training_total();
    # List songs by when they were last practiced, NOT by total duration.
    # The snapshot also supplies a chronological tie-breaker if two songs
    # happen to have the same last-practiced timestamp.
    my @segments = session_segments_snapshot();
    my %last_segment_order;
    for my $i (0 .. $#segments) {
        my $id = $segments[$i]->{song_id} // '';
        $last_segment_order{$id} = $i if length $id;
    }
    my @ids = sort {
        ($song_last_practiced_epoch{$b} // 0) <=> ($song_last_practiced_epoch{$a} // 0)
            || ($last_segment_order{$b} // -1) <=> ($last_segment_order{$a} // -1)
            || lc($song_titles{$a} // $a) cmp lc($song_titles{$b} // $b)
    } grep { ($song_elapsed{$_} // 0) > 0.001 } keys %song_elapsed;
    my $total_selections = 0;
    $total_selections += $song_practice_starts{$_} // 0 for @ids;

    # Supplemental categories join the song list, but remain category-only
    # time: no one-minute song-selection rule and no song selection count.
    my @practice_entries = map {
        {
            kind  => 'song',
            id    => $_,
            title => $song_titles{$_} // $_,
            last  => $song_last_practiced_epoch{$_} // 0,
            order => $last_segment_order{$_} // -1,
        }
    } @ids;

    # List each supplemental activity separately, ordered alongside songs.
    # Like Scales, Ear training does not create song selection counts.
    for my $supplemental (
        { key => scales_key(), name => 'Scales', kind => 'scales', total => $scales },
        { key => ear_training_key(), name => 'Ear training', kind => 'ear_training', total => $ear_training },
    ) {
        next unless defined($supplemental->{key}) && $supplemental->{total} > 0.001;
        my ($last, $order) = (0, -1);
        for my $i (0 .. $#segments) {
            my $seg = $segments[$i];
            next unless ($seg->{key} // '') eq $supplemental->{key};
            next unless ($seg->{seconds} // 0) > 0.001;
            my $end = $seg->{end_epoch} // 0;
            if ($end >= $last) {
                $last = $end;
                $order = $i;
            }
        }
        push @practice_entries, {
            kind => $supplemental->{kind},
            id => $supplemental->{key},
            title => $supplemental->{name},
            last => $last,
            order => $order,
        };
    }

    @practice_entries = sort {
        $b->{last} <=> $a->{last}
            || $b->{order} <=> $a->{order}
            || lc($a->{title}) cmp lc($b->{title})
    } @practice_entries;

    return (\@practice_entries, scalar(@ids), $total_selections);
}

sub format_current_session_details {
    my $now = time;
    my $line = '-' x 74;
    my $heavy = '=' x 74;
    my $active = reported_active_total();
    my $target = repertoire_total();
    my $theory = theory_total();
    my $scales = scales_total();
    my $ear_training = ear_training_total();
    my $pause = $elapsed{pause_key()} // 0;
    my $clock = session_elapsed();

    my ($entries, $song_count, $total_selections) = session_view_entries();
    my @practice_entries = @$entries;

    my $out = "$heavy\n";
    $out .= "                        CURRENT PRACTICE SESSION\n";
    $out .= "$heavy\n";
    $out .= '  Started  ' . strftime('%a, %b %d %Y', localtime($session_start))
        . ' at ' . session_view_time($session_start) . "\n";
    $out .= '  Updated  ' . strftime('%a, %b %d %Y', localtime($now))
        . ' at ' . session_view_time($now) . "\n\n";

    $out .= "  PRACTICED        " . fmt_time($active) . "    (includes Theory, Scales and Ear training)\n";
    $out .= "  SESSION CLOCK    " . fmt_time($clock) . "\n";
    $out .= "  PAUSED           " . fmt_time($pause) . "\n";
    $out .= "  Repertoire       " . fmt_time($target) . "    Theory  " . fmt_time($theory) . "    Scales  " . fmt_time($scales) . "    Ear  " . fmt_time($ear_training) . "\n";
    $out .= "\n  CURRENT SELECTION\n";
    $out .= "  $line\n";
    $out .= '  [' . $current_key . '] ' . $by_key{$current_key}->{name} . "\n";
    $out .= length $current_song_id
        ? '  ' . session_view_wrap($current_song_title, 69, '  ') . "\n"
        : ($current_key eq pause_key() && length $resume_key)
            ? '  Paused from [' . $resume_key . '] '
                . session_view_wrap(length($resume_song_title)
                    ? $resume_song_title : $by_key{$resume_key}->{name}, 55, '  ')
                . " (p to resume)\n"
            : "  No individual song selected\n";

    $out .= "\n  PRACTICE BREAKDOWN\n";
    $out .= "  $line\n";
    $out .= "  Category                          Duration   Share   Distribution\n";
    my @used_categories = sort {
        ($elapsed{$b->{key}} // 0) <=> ($elapsed{$a->{key}} // 0)
    } grep { !$_->{is_pause} && !$_->{is_adjust} && !$_->{is_scales} && !$_->{is_ear_training}
        && $_->{key} ne 'y' && !$_->{is_retired}
        && ($elapsed{$_->{key}} // 0) > 0.001 } @options;
    if (!@used_categories && $theory <= 0.001 && $scales <= 0.001 && $ear_training <= 0.001) {
        $out .= "  No practice recorded yet.\n";
    }
    else {
        for my $option (@used_categories) {
            my $key = $option->{key};
            my $percent = percent_for($key);
            my $bar = session_view_bar($percent, 14);
            $out .= sprintf("  %-32s %8s  %3d%%   [%s]\n",
                "[$key] " . $option->{name}, fmt_time($elapsed{$key}),
                int($percent + 0.5), $bar);
        }
        if ($theory > 0.001) {
            $out .= sprintf("  %-32s %8s    --   (tracked separately)\n",
                'Theory', fmt_time($theory));
        }
        if ($scales > 0.001) {
            $out .= sprintf("  %-32s %8s    --   (tracked separately)\n",
                'Scales', fmt_time($scales));
        }
        if ($ear_training > 0.001) {
            $out .= sprintf("  %-32s %8s    --   (tracked separately)\n",
                'Ear training', fmt_time($ear_training));
        }
    }
    $out .= "  Shares are of repertoire-category time; Theory, Scales, Ear training, and Pause are excluded.\n";

    $out .= "\n  SONGS PRACTICED + SCALES + EAR TRAINING  (most recent first; " . $song_count . ' songs, '
        . "$total_selections song selections)\n";
    $out .= "  $line\n";
    if (!@practice_entries) {
        $out .= "  No individual songs, Scales, or Ear training tracked yet.\n";
    }
    else {
        my $rank = 0;
        for my $entry (@practice_entries) {
            $rank++;
            my $duration = $entry->{kind} eq 'scales'
                ? fmt_time($scales)
                : $entry->{kind} eq 'ear_training'
                    ? fmt_time($ear_training)
                    : fmt_time($song_elapsed{$entry->{id}} // 0);
            my $last = $entry->{last};
            my $last_text = $last > 0 ? session_view_time($last) : 'unknown';
            $out .= sprintf("  %2d. %s\n", $rank, session_view_wrap($entry->{title}, 65, '      '));
            if ($entry->{kind} eq 'scales' || $entry->{kind} eq 'ear_training') {
                $out .= sprintf("      %s practiced   |   %s category   |   last at %s\n",
                    $duration, $entry->{title}, $last_text);
            }
            else {
                my $selections = $song_practice_starts{$entry->{id}} // 0;
                $out .= sprintf("      %s practiced   |   %d %s   |   last at %s\n",
                    $duration, $selections,
                    $selections == 1 ? 'selection' : 'selections', $last_text);
            }
        }
    }

    # Chronological segments are still recorded and used for song ordering,
    # but are intentionally hidden from the current-session display.
    $out .= "$heavy\n";
    return $out;
}

# A View entry represents ALL practice for that song in the CURRENT timer
# session. It is NOT a repertoire entry. Neither the song catalog nor any
# media attachment, dated adjustment, or other session is removed.
sub view_entry_deletion_plan {
    my ($entry) = @_;

    # Song/category adjustments update credited totals but do not retroactively
    # rewrite the chronological timeline.  Therefore timeline seconds can be
    # LARGER than the time the song is still credited with.  Credited totals
    # are authoritative when deciding how much category time can be removed.
    my $recorded = $entry->{kind} eq 'scales'
        ? scales_total() : $entry->{kind} eq 'ear_training'
            ? ear_training_total() : ($song_elapsed{$entry->{id}} // 0);
    $recorded = 0 if $recorded < 0;

    my @matching_segments;
    my $original_timed_total = 0;
    for my $i (0 .. $#session_segments) {
        my $segment = $session_segments[$i];
        my $matches = $entry->{kind} eq 'scales'
            ? (($segment->{key} // '') eq scales_key())
            : $entry->{kind} eq 'ear_training'
                ? (($segment->{key} // '') eq ear_training_key())
                : (($segment->{song_id} // '') eq $entry->{id});
        next unless $matches;
        my $seconds = $segment->{seconds} // 0;
        next unless $seconds > 0;
        my $key = $segment->{key} // '';
        next unless exists $elapsed{$key} && !$by_key{$key}{is_pause}
            && !$by_key{$key}{is_adjust};
        push @matching_segments, { index => $i, seconds => $seconds, key => $key };
        $original_timed_total += $seconds;
    }

    # Allocate the credited portion to the most recent matching blocks first.
    # In the common case (no negative adjustment), this retains every block.
    # When an adjustment has reduced the song total, it prevents removing old,
    # no-longer-credited hours from unrelated category practice.
    my %credited_segments;
    my %category_seconds;
    my $remaining = $recorded;
    my $timed_total = 0;
    for my $block (reverse @matching_segments) {
        last if $remaining <= 0.001;
        my $credit = $block->{seconds} < $remaining
            ? $block->{seconds} : $remaining;
        next unless $credit > 0.001;
        $credited_segments{$block->{index}} = $credit;
        $category_seconds{$block->{key}} += $credit;
        $timed_total += $credit;
        $remaining -= $credit;
    }

    # Positive manual additions are not timeline segments.  As before, the
    # user chooses whether their category total should also be reduced.
    my $unattributed = $recorded - $timed_total;
    $unattributed = 0 if $unattributed < 0.001;
    return {
        recorded => $recorded,
        original_timed => $original_timed_total,
        timed => $timed_total,
        manual => $unattributed,
        categories => \%category_seconds,
        credited_segments => \%credited_segments,
    };
}

sub view_entry_default_category {
    my ($entry) = @_;
    return scales_key() if $entry->{kind} eq 'scales';
    return ear_training_key() if $entry->{kind} eq 'ear_training';
    my ($records) = read_song_categories_tsv($SONG_CATEGORY_FILE);
    if (defined $records) {
        for my $record (@$records) {
            return '' . $record->{level}
                if ($record->{song_id} // '') eq $entry->{id};
        }
    }
    return '';
}

# Filter only rows belonging to the current session and selected song. Use a
# full copy as a rollback backup before touching original logs. Preserve all
# other bytes, including the old TSV header/layout and past snapshots.
sub rewrite_view_deletion_log {
    my ($file, $kind, $entry_id) = @_;
    return 0 unless -e $file;
    open my $in, '<', $file or die "Could not read $file: $!";
    binmode $in;
    my $tag = strftime('%Y%m%d_%H%M%S', localtime(time));
    my $tmp = "$file.view-delete-$tag-$$.tmp";
    my $number = 2;
    while (-e $tmp) { $tmp = "$file.view-delete-$tag-$$-$number.tmp"; $number++; }
    open my $out, '>', $tmp or die "Could not write $tmp: $!";
    binmode $out;
    my $removed = 0;
    my $ok = eval {
        while (my $line = <$in>) {
            my @fields = split /\t/, $line, -1;
            my $matches = ($fields[0] // '') eq $session_start_stamp;
            $matches &&= ($fields[2] // '') eq $entry_id if $kind eq 'song';
            if ($matches) { $removed++; next; }
            print {$out} $line or die "Could not write $tmp: $!";
        }
        close($out) or die "Could not close $tmp: $!";
        close($in) or die "Could not close $file: $!";
        1;
    };
    if (!$ok) {
        my $error = $@ || 'Unknown TSV write error';
        close $out;
        close $in;
        unlink $tmp;
        die $error;
    }
    my $parked = "$file.view-delete-$tag-$$.old";
    my $park_number = 2;
    while (-e $parked) {
        $parked = "$file.view-delete-$tag-$$-$park_number.old";
        $park_number++;
    }
    rename($file, $parked)
        or do { unlink $tmp; die "Could not temporarily move $file: $!"; };
    unless (rename($tmp, $file)) {
        my $error = $!;
        rename($parked, $file);
        unlink $tmp;
        die "Could not replace $file: $error";
    }
    unlink $parked;
    return $removed;
}

sub view_deletion_backups {
    my @files = ($STATE_FILE, $LOG_FILE, $SONG_LOG_FILE);
    my %backup;
    my $tag = strftime('%Y%m%d_%H%M%S', localtime(time));
    for my $file (@files) {
        if (!-e $file) { $backup{$file} = undef; next; }
        my $path = "$file.before_view_delete_$tag.bak";
        my $suffix = 2;
        while (-e $path) { $path = "$file.before_view_delete_${tag}_$suffix.bak"; $suffix++; }
        copy($file, $path) or die "Could not back up $file to $path: $!";
        $backup{$file} = $path;
    }
    return \%backup;
}

# All mutation is in one routine for testing independently of the UI. Timed
# practice is reclassified as Pause, exactly as Undo does, preserving the
# running session clock. For manual song credit lacking timeline evidence,
# category deduction requires an explicit user choice; song-only adjustments
# must not silently alter category totals.
sub apply_view_practice_deletion {
    my ($entry, $manual_category) = @_;
    my $plan = view_entry_deletion_plan($entry);
    my %deduct = %{ $plan->{categories} };
    if ($entry->{kind} eq 'scales' || $entry->{kind} eq 'ear_training') {
        # Supplemental categories have their own identity, even for adjustments.
        $deduct{view_entry_default_category($entry)} += $plan->{manual};
    }
    elsif (defined($manual_category) && length($manual_category)) {
        $deduct{$manual_category} += $plan->{manual};
    }
    for my $key (keys %deduct) {
        return (0, "Cannot delete safely: unknown practice category [$key].")
            unless exists $elapsed{$key} && !$by_key{$key}{is_pause}
                && !$by_key{$key}{is_adjust};
        return (0, "Cannot delete safely: category [$key] has only "
            . fmt_time($elapsed{$key}) . ' but this deletion requires '
            . fmt_time($deduct{$key}) . '. No changes made.')
            if ($elapsed{$key} // 0) + 0.01 < $deduct{$key};
    }

    my $backup;
    eval { $backup = view_deletion_backups(); 1; }
        or do {
            my $error = $@ || 'Unknown backup error';
            $error =~ s/\s+\z//;
            return (0, "Deletion canceled: $error");
        };

    my %old_elapsed = %elapsed;
    my %old_song_elapsed = %song_elapsed;
    my %old_song_titles = %song_titles;
    my %old_starts = %song_practice_starts;
    my %old_last = %song_last_practiced_epoch;
    my @old_segments = map { { %$_ } } @session_segments;
    my ($old_key, $old_song_id, $old_song_title) =
        ($current_key, $current_song_id, $current_song_title);
    my ($old_sel_seconds, $old_sel_qualified, $old_sel_id, $old_undo) =
        ($current_selection_seconds, $current_selection_qualified,
         $current_selection_id, $undo_locked);
    my @old_resume = ($resume_key, $resume_song_id, $resume_song_title,
        $resume_selection_seconds, $resume_selection_qualified, $resume_selection_id);

    my ($song_rows_removed, $master_rows_removed) = (0, 0);
    my $success = eval {
        # Remove all of this entry's original timeline blocks, but only
        # transfer the still-credited portion to Pause.  In particular, after
        # a negative manual adjustment an old three-hour segment must NOT
        # become three hours of Pause when only a minute remains credited.
        my @kept_segments;
        for my $i (0 .. $#session_segments) {
            my $segment = $session_segments[$i];
            my $matches = $entry->{kind} eq 'scales'
                ? (($segment->{key} // '') eq scales_key())
                : $entry->{kind} eq 'ear_training'
                    ? (($segment->{key} // '') eq ear_training_key())
                    : (($segment->{song_id} // '') eq $entry->{id});
            if (!$matches || ($segment->{seconds} // 0) <= 0) {
                push @kept_segments, $segment;
                next;
            }
            my $credited = $plan->{credited_segments}{$i} // 0;
            next unless $credited > 0.001; # Already removed by an adjustment.
            if ($credited < ($segment->{seconds} // 0)) {
                # Retain the latest portion of a partly adjusted segment.
                $segment->{seconds} = $credited;
                my $end_epoch = $segment->{end_epoch} // 0;
                $segment->{start_epoch} = $end_epoch - $credited
                    if $end_epoch > 0 && $end_epoch - $credited > ($segment->{start_epoch} // 0);
            }
            $elapsed{pause_key()} += $credited;
            $segment->{key} = pause_key();
            $segment->{song_id} = '';
            $segment->{song_title} = '';
            $segment->{selection_id} = 0;
            push @kept_segments, $segment;
        }
        @session_segments = @kept_segments;
        for my $key (keys %deduct) {
            $elapsed{$key} -= $deduct{$key};
            $elapsed{$key} = 0 if $elapsed{$key} < 0.01;
        }
        if ($entry->{kind} eq 'scales' || $entry->{kind} eq 'ear_training') {
            my $supplemental_key = view_entry_default_category($entry);
            $current_key = pause_key() if $current_key eq $supplemental_key;
            clear_resume_selection() if $resume_key eq $supplemental_key;
        }
        else {
            my $id = $entry->{id};
            clear_resume_selection() if $resume_song_id eq $id;
            delete $song_elapsed{$id};
            delete $song_titles{$id};
            delete $song_practice_starts{$id};
            delete $song_last_practiced_epoch{$id};
            if ($current_song_id eq $id) {
                clear_current_song();
                $current_key = pause_key();
            }
            $displayed_tip_song_id = '' if $displayed_tip_song_id eq $id;
            $song_rows_removed = rewrite_view_deletion_log(
                $SONG_LOG_FILE, 'song', $id);
        }
        # Replacing current-session master snapshots also removes stale rows
        # if the corrected session is now shorter than the logging threshold.
        $master_rows_removed = rewrite_view_deletion_log(
            $LOG_FILE, 'session', '');
        $undo_locked = 1;
        save_all();
        1;
    };
    unless ($success) {
        my $error = $@ || 'Unknown deletion error';
        %elapsed = %old_elapsed;
        %song_elapsed = %old_song_elapsed;
        %song_titles = %old_song_titles;
        %song_practice_starts = %old_starts;
        %song_last_practiced_epoch = %old_last;
        @session_segments = @old_segments;
        ($current_key, $current_song_id, $current_song_title) =
            ($old_key, $old_song_id, $old_song_title);
        ($current_selection_seconds, $current_selection_qualified,
         $current_selection_id, $undo_locked) =
            ($old_sel_seconds, $old_sel_qualified, $old_sel_id, $old_undo);
        ($resume_key, $resume_song_id, $resume_song_title,
         $resume_selection_seconds, $resume_selection_qualified,
         $resume_selection_id) = @old_resume;
        for my $file ($STATE_FILE, $LOG_FILE, $SONG_LOG_FILE) {
            if (defined $backup->{$file}) {
                copy($backup->{$file}, $file)
                    or $error .= " (WARNING: restore $file failed: $!)";
            }
            else { unlink $file if -e $file; }
        }
        $error =~ s/\s+\z//;
        return (0, "Deletion failed; attempted to restore original data. $error");
    }
    my $description = $entry->{title};
    my $audit_note = audit_write({ action => 'PRACTICE_ENTRY_REMOVED',
        id => $entry->{id}, old => fmt_time($plan->{recorded}), new => '00:00:00',
        detail => "Current session $session_start_stamp; $description" });
    return (1, "Removed '$description' from this session ("
        . fmt_time($plan->{recorded}) . "). Removed $song_rows_removed song-log"
        . " snapshots and replaced $master_rows_removed session-log snapshots."
        . ' Backup copies of the original state/log files were kept.' . $audit_note);
}

sub prompt_delete_view_practice_entry {
    my ($entry) = @_;
    my $plan = view_entry_deletion_plan($entry);
    print "\nDELETE CURRENT-SESSION PRACTICE\n";
    print "-------------------------------\n";
    print "Entry:     $entry->{title}\n";
    print 'Credited:  ' . fmt_time($plan->{recorded}) . "\n";
    if ($plan->{original_timed} > $plan->{timed} + 0.01) {
        print 'Original timed segments (before adjustments): '
            . fmt_time($plan->{original_timed}) . "\n";
        print "  Some of that time was already removed by an adjustment.\n";
    }
    print 'Still-credited timed practice to remove from category totals: '
        . fmt_time($plan->{timed}) . "\n";
    print "Other sessions, repertoire, and media attachments will not be touched.\n";
    print "The program will back up the state and affected TSV logs first.\n";

    my $manual_category = '';
    if ($entry->{kind} eq 'song' && $plan->{manual} > 0.01) {
        my $category = view_entry_default_category($entry);
        my $label = length($category) ? "[$category] "
            . ($by_key{$category}{name} // '') : '(unknown category)';
        print "\nThis entry includes " . fmt_time($plan->{manual})
            . " of song credit without matching timed blocks.\n";
        print "It may have been added manually. The program cannot tell\n";
        print "whether the category was also adjusted or this was song-only (!).\n";
        print "Also subtract that time from category $label? [N/y]: ";
        my $choice = <STDIN>;
        if (defined $choice && $choice =~ /\A\s*y\s*\z/i) {
            if (!length($category)) {
                print "Category key to subtract (0-6, y; Enter=cancel): ";
                my $key = <STDIN>;
                return (0, 'Canceled.') unless defined $key;
                $category = lc trim_text($key);
            }
            return (0, 'Invalid category; no changes made.')
                unless exists $by_key{$category}
                    && !$by_key{$category}{is_pause}
                    && !$by_key{$category}{is_adjust}
                    && !$by_key{$category}{is_retired}
                    && !$by_key{$category}{is_scales}
                    && !$by_key{$category}{is_ear_training};
            $manual_category = $category;
        }
    }
    print "\nDelete this practice entry and its current-session log snapshots? [y/N]: ";
    my $confirm = <STDIN>;
    return (0, 'Deletion canceled.')
        unless defined($confirm) && $confirm =~ /\A\s*y\s*\z/i;
    return apply_view_practice_deletion($entry, $manual_category);
}

sub show_current_session_details {
    ReadMode('restore');
    my $first_page = 1;
    while (1) {
        # Keep overview and the numbered song/Scales list on separate pages.
        my ($overview, $songs) = split /(?=^  SONGS PRACTICED\b)/m,
            format_current_session_details(), 2;
        if ($first_page) {
            print_paged_song_categories($overview);
            if (defined $songs) {
                print "\nPress any key to view songs, Scales, and Ear training practiced...";
                ReadMode('cbreak');
                ReadKey(0);
                ReadMode('restore');
            }
        }
        print_paged_song_categories($songs) if defined $songs;
        my ($entries) = session_view_entries();
        last unless @$entries;
        print "\nDelete entry (1-" . scalar(@$entries)
            . "), or Enter to return to the timer: ";
        my $answer = <STDIN>;
        last unless defined $answer;
        chomp $answer;
        $answer = trim_text($answer);
        last unless length $answer;
        if ($answer !~ /\A\d+\z/ || $answer < 1 || $answer > @$entries) {
            print "\nInvalid entry number. Press Enter to retry...";
            scalar <STDIN>;
            $first_page = 0;
            next;
        }
        my ($ok, $message) = prompt_delete_view_practice_entry(
            $entries->[$answer - 1]);
        print "\n$message\n";
        print "Press Enter to see the updated song list...";
        scalar <STDIN>;
        $first_page = 0;
    }

    # The detailed activity report now has its own l main-screen shortcut.
    # View no longer opens or prompts for the report.
    ReadMode('cbreak');
    $last_tick = time;
}

# The l-key report reads saved TSV snapshots, so save the latest session
# first. Existing one-minute minimums and snapshot de-duplication still apply.
# Catch file errors so a report failure doesn't terminate the running timer.
sub refresh_activity_report_for_gvim {
    my ($ok, $message);
    my $completed = eval {
        save_all();
        ($ok, $message) = write_activity_report($LOG_FILE, $REPORT_FILE);
        1;
    };
    if (!$completed) {
        my $error = $@ || 'Unknown file error';
        $error =~ s/\s+\z//;
        return (0, "Could not refresh $REPORT_FILE: $error");
    }
    return ($ok, $message);
}

# Generate the latest statistics and open them in gVim immediately.
# This is called only by l from the main screen; no nested menu or prompt.
sub open_updated_activity_report_in_gvim {
    my ($ok, $message) = refresh_activity_report_for_gvim();
    return $message unless $ok;

    # The activity report uses gVim, not the TXT attachment editor setting.
    my $report_path = File::Spec->rel2abs($REPORT_FILE);
    my $error = launch_song_material_program(gvim_program(), '--', $report_path);
    return length($error) ? $error : "Opened $REPORT_FILE in gVim.";
}

sub show_descriptions {
    ReadMode('restore');

    clear_screen();

    print "Category Descriptions\n";
    print "=====================\n\n";

    for my $option (@options) {
        next if $option->{is_adjust} || $option->{is_retired};

        print "[$option->{key}] $option->{name}\n";
        print "Target: " . target_label($option) . "\n";

        if (defined $option->{desc} && length $option->{desc}) {
            print "$option->{desc}\n";
        }
        else {
            print "No description available.\n";
        }

        print "\n";
    }

    print "Press Enter to return to the timer...";
    scalar <STDIN>;

    ReadMode('cbreak');

    # Prevent reading time from being added to the current category.
    $last_tick = time;
}

# Main-screen z shortcut: printable repertoire overview, not the detailed
# d-key category descriptions. Reading the page is not practice time.
sub show_repertoire_guide {
    clear_screen();

    print <<'REPERTOIRE_GUIDE';
REPERTOIR GUIDE

Keystones / Landmarks (0–5%) (1 to 2 songs)
Songs of special personal significance that have become part of my musical identity.

Ready Core (20–30%) (5 to 10 songs)
Songs I can already play and want to keep performance-ready.

Active Development (30–40%) (5 to 8 songs)
Songs I'm actively working to improve or master. My primary practice focus.

Incubator / Candidates (10–20%) (2 to 4 songs)
New songs I'm experimenting with before deciding whether to pursue them seriously.

Maintenance / Rotation (5–15%) (5 to 10 songs)
Familiar songs that need occasional attention to keep them fresh.

Back Burner (0–10%) (Unlimited songs)
Songs I want to retain but am not actively prioritizing.

Cold Storage (No Target) (Unlimited songs)
Songs I've learned and consider accomplishments, but which no longer require regular practice.
REPERTOIRE_GUIDE

    print "\nPress any key to continue...";
    ReadKey(0);
    $last_tick = time;
}

sub option_for_level {
    my ($level) = @_;

    # Categories and activities such as Theory are not repertoire levels.
    return undef unless defined($level) && $level =~ /^[0-6]$/;

    for my $option (@options) {
        next if $option->{is_pause} || $option->{is_adjust} || $option->{is_scales} || $option->{is_ear_training} || $option->{is_retired};
        return $option if $option->{key} eq $level;
    }

    return undef;
}

sub valid_song_level {
    my ($level) = @_;
    return defined option_for_level($level);
}

sub level_label {
    my ($level) = @_;

    my $option = option_for_level($level);
    return "Level $level - $option->{name}" if defined $option;
    return "Level $level";
}

sub trim_text {
    my ($value) = @_;
    $value //= '';
    $value =~ s/^\s+//;
    $value =~ s/\s+\z//;
    return $value;
}

sub song_id_slug {
    my ($value) = @_;
    $value = lc trim_text($value);
    $value =~ s/[^a-z0-9]+/_/g;
    $value =~ s/^_+//;
    $value =~ s/_+\z//;
    return length($value) ? $value : 'song';
}

sub clean_song_id {
    my ($value) = @_;
    $value = song_id_slug($value);
    return $value;
}

# Used to prevent accidental duplicate repertoire entries. Different case and
# spacing do not make a second, distinct song. Attach multiple recordings to
# one song ID rather than adding the same title a second time.
sub song_title_identity {
    my ($value) = @_;
    $value = lc trim_text($value);
    $value =~ s/\s+/ /g;
    return $value;
}

sub duplicate_song_title {
    my ($records) = @_;
    my %first;
    for my $record (@$records) {
        my $key = song_title_identity($record->{title});
        return ($first{$key}, $record) if exists $first{$key};
        $first{$key} = $record;
    }
    return ();
}

sub ensure_song_ids {
    my ($records, $warnings) = @_;
    $warnings //= [];

    my %used;
    my $changed = 0;

    for my $record (@$records) {
        # Never rewrite an existing, nonblank fourth-column handle.
        # Handles are stable even when titles and category positions change.
        my $id = trim_text($record->{song_id} // '');

        if ($id ne '' && $id ne $SCALES_ATTACHMENT_ID && $id ne $EAR_TRAINING_ATTACHMENT_ID && $id ne $JAMMING_ATTACHMENT_ID && $id ne $THEORY_ATTACHMENT_ID && !$used{$id}) {
            if (!defined($record->{song_id}) || $record->{song_id} ne $id) {
                $record->{song_id} = $id;
                $changed = 1;
            }
            $used{$id} = 1;
        }
        else {
            $record->{song_id} = undef;
            $changed = 1;
        }
    }

    for my $record (@$records) {
        next if defined($record->{song_id}) && length($record->{song_id});

        my $base = song_id_slug($record->{title});
        my $id = $base;
        my $suffix = 2;

        while ($used{$id} || $id eq $SCALES_ATTACHMENT_ID || $id eq $EAR_TRAINING_ATTACHMENT_ID || $id eq $JAMMING_ATTACHMENT_ID || $id eq $THEORY_ATTACHMENT_ID) {
            $id = $base . '_' . $suffix;
            $suffix++;
        }

        $record->{song_id} = $id;
        $used{$id} = 1;
        $changed = 1;
    }

    push @$warnings,
        "Generated stable song IDs for rows that did not have them. The category TSV will now use four columns."
        if $changed;

    return $changed;
}

# Audit events are emitted ONLY after the corresponding data file was saved.
# An audit failure is reported prominently; it must never be mistaken for a
# successful audit entry. The data change is not retroactively rolled back.
sub audit_write {
    my (@events) = @_;
    my ($ok, $error) = append_events($AUDIT_FILE, \@events);
    if (!$ok) {
        my $warning = "AUDIT LOG ERROR: $error (data change was saved).";
        warn "\n$warning\n";
        $last_message = $warning;
        $audit_alert = $warning;
        return " $warning";
    }
    return '';
}

# Compare attached files by persistent song/activity ID. This captures
# explicit attachment edits and automatic candidate approvals alike.
sub audit_media_changes {
    my ($old, $new, $kind) = @_;
    my @events;
    for my $id (sort keys %{ { %$old, %$new } }) {
        my %before = map { lc($_) => $_ } @{ $old->{$id} // [] };
        my %after  = map { lc($_) => $_ } @{ $new->{$id} // [] };
        for my $k (sort keys %before) {
            next if exists $after{$k};
            push @events, { action => 'MEDIA_REMOVED', id => $id,
                old => $before{$k}, new => '', detail => $kind };
        }
        for my $k (sort keys %after) {
            next if exists $before{$k};
            push @events, { action => 'MEDIA_ATTACHED', id => $id,
                old => '', new => $after{$k}, detail => $kind };
        }
    }
    return audit_write(@events);
}

sub audit_sheet_changes {
    my ($before, $after) = @_;
    my (%a, %b);
    for my $row (@$before) {
        $a{$row->{song_id}}{$row->{target}}++;
    }
    for my $row (@$after) {
        $b{$row->{song_id}}{$row->{target}}++;
    }
    my @events;
    for my $id (sort keys %{ { %a, %b } }) {
        my $old = $a{$id} // {};
        my $new = $b{$id} // {};
        for my $path (sort keys %{ { %$old, %$new } }) {
            my $delta = ($new->{$path} // 0) - ($old->{$path} // 0);
            my $action = $delta > 0 ? 'MEDIA_ATTACHED' : 'MEDIA_REMOVED';
            for (1 .. abs($delta)) {
                push @events, { action => $action, id => $id,
                    old => $delta < 0 ? $path : '', new => $delta > 0 ? $path : '',
                    detail => 'sheet_music' };
            }
        }
    }
    return audit_write(@events);
}

sub view_audit_log {
    unless (-e $AUDIT_FILE && -s $AUDIT_FILE) {
        return "No audit events recorded yet. Future changes will appear in $AUDIT_FILE.";
    }
    my $err = launch_song_material_program(notepad_program(), $AUDIT_FILE);
    return length($err) ? $err : "Opened $AUDIT_FILE in Notepad.";
}

sub read_song_categories_tsv {
    my ($file) = @_;
    $file //= $SONG_CATEGORY_FILE;

    return (undef, ["Song category file not found: $file"])
        unless -e $file;

    open my $fh, '<', $file
        or return (undef, ["Could not read $file: $!"]);

    my @records;
    my @warnings;
    my @pending_comments;
    my @header_comments;
    my $line_no = 0;

    while (my $line = <$fh>) {
        $line_no++;
        chomp $line;
        $line =~ s/\r\z//;

        # Whole-line # comments are valid input and must survive edits.
        # Hold each comment until its following song has been validated;
        # comments before the first song belong to the file header.
        if ($line =~ /^[ \t]*#/) {
            push @pending_comments, $line;
            next;
        }

        # The TSV may contain visual spacing. Ignore wholly empty/whitespace rows,
        # including rows made only from tabs and spaces.
        next if $line =~ /^\s*\z/;

        # Current format:
        #   level<TAB>number<TAB>title<TAB>song_id[<TAB>archived]
        # Four-column and legacy three-column rows still load unchanged.
        # An archived fifth column hides the song without deleting it or
        # changing the permanent song_id used in practice/media history.
        my ($level, $number, $title, $song_id, $status) = split /\t/, $line, 5;
        $level   = trim_text($level);
        $number  = trim_text($number);
        $title   = trim_text($title);
        $song_id = trim_text($song_id);
        $status  = lc trim_text($status);
        if (length($status) && $status ne 'archived') {
            push @warnings, "Line $line_no has unknown archive status '$status'; treating it as active.";
        }

        if ($level !~ /^\d+\z/ || $number !~ /^\d+\z/ || $title eq '') {
            push @warnings, "Line $line_no ignored: expected level<TAB>number<TAB>title<TAB>optional_song_id.";
            next;
        }

        if (!valid_song_level($level)) {
            push @warnings, "Line $line_no ignored: unknown song level $level.";
            next;
        }

        my $record = {
            level   => 0 + $level,
            number  => 0 + $number,
            title   => $title,
            song_id  => length($song_id) ? $song_id : undef,
            archived => ($status eq 'archived' ? 1 : 0),
            line_no  => $line_no,
        };
        if (!@records) {
            push @header_comments, @pending_comments;
        }
        elsif (@pending_comments) {
            $record->{leading_comments} = [ @pending_comments ];
        }
        @pending_comments = ();
        push @records, $record;
    }

    close $fh;
    # Comments after the final song, or in a file with no song rows,
    # remain at the end rather than being silently discarded on save.
    $song_category_comment_layout{$file} = {
        header => [ @header_comments ],
        footer => [ @pending_comments ],
    };

    # Detect corrupt/imported duplicates, but NEVER delete rows silently:
    # some may have historical song IDs or media references. The repair tool
    # can reconcile those references before replacing the catalog.
    my %seen_titles;
    for my $record (@records) {
        my $key = song_title_identity($record->{title});
        if (exists $seen_titles{$key}) {
            my $original = $seen_titles{$key};
            push @warnings, "Duplicate song '$record->{title}' on lines "
                . "$original->{line_no} and $record->{line_no}. "
                . "The catalog needs repair; automatic saving of duplicates is blocked.";
        }
        else {
            $seen_titles{$key} = $record;
        }
    }

    # Treat the second TSV column as ordering data, but make the displayed
    # and selectable song number be the current position within that level.
    # This lets a level whose file rows start at 2/3 still be selected as
    # 0 1 / 0 2 on the category screen.
    normalize_song_numbers(\@records);
    my $ids_changed = ensure_song_ids(\@records, \@warnings);

    return (\@records, \@warnings, $ids_changed);
}

sub group_song_categories_by_level {
    my ($records, $include_archived) = @_;

    my %by_level;

    for my $record (@$records) {
        next if !$include_archived && $record->{archived};
        push @{ $by_level{ $record->{level} } }, $record;
    }

    for my $level (keys %by_level) {
        @{ $by_level{$level} } = sort {
            ($a->{archived} // 0) <=> ($b->{archived} // 0)
                || $a->{number} <=> $b->{number}
                || ($a->{line_no} // 0) <=> ($b->{line_no} // 0)
                || lc($a->{title}) cmp lc($b->{title})
        } @{ $by_level{$level} };
    }

    return \%by_level;
}

sub normalize_song_numbers {
    my ($records) = @_;

    my $by_level = group_song_categories_by_level($records);

    for my $level (keys %$by_level) {
        my $number = 1;
        for my $record (@{ $by_level->{$level} }) {
            $record->{number} = $number++;
        }
    }

    return $records;
}

sub write_song_categories_tsv {
    my ($records, $file) = @_;
    $file //= $SONG_CATEGORY_FILE;

    # Fail closed rather than persisting another duplicated catalog. The
    # legitimate multiple MP3/tab attachments live in separate TSVs.
    my ($first, $second) = duplicate_song_title($records);
    if (defined $first) {
        return (0, "Refusing to overwrite $file: duplicate title '$second->{title}' "
            . "(song IDs " . ($first->{song_id} // '[missing]') . " and "
            . ($second->{song_id} // '[missing]') . "). Fix duplicates first.");
    }

    normalize_song_numbers($records);
    ensure_song_ids($records);

    # Keep archived rows in the TSV even though routine display/list/search
    # functions exclude them. This is deliberately a reversible archive.
    my $by_level = group_song_categories_by_level($records, 1);
    my @levels = sort { $a <=> $b } keys %$by_level;

    open my $fh, '>', $file
        or return (0, "Could not write $file: $!");

    my $layout = $song_category_comment_layout{$file} // {};
    my $header = $layout->{header} // [];
    my $footer = $layout->{footer} // [];
    for my $comment (@$header) {
        print {$fh} "$comment\n";
    }
    print {$fh} "\n" if @$header && @levels;

    my $first_level = 1;
    for my $level (@levels) {
        print {$fh} "\n" unless $first_level;
        $first_level = 0;

        my $first_song = 1;
        for my $record (@{ $by_level->{$level} }) {
            my $comments = $record->{leading_comments} // [];
            if (@$comments) {
                # A comment for a song moves with that song when its category
                # or position changes, rather than getting left behind.
                print {$fh} "\n" unless $first_song;
                print {$fh} "$_\n" for @$comments;
            }
            my @columns = (
                $record->{level},
                $record->{number},
                $record->{title},
                $record->{song_id},
            );
            push @columns, 'archived' if $record->{archived};
            print {$fh} join("\t", @columns), "\n";
            $first_song = 0;
        }
    }

    print {$fh} "\n" if @$footer && @levels;
    print {$fh} "$_\n" for @$footer;

    close $fh or return (0, "Could not finish writing $file: $!");
    return (1, "Saved song categories to $file.");
}

sub find_song_record {
    my ($records, $level, $number) = @_;

    for my $record (@$records) {
        return $record
            if !$record->{archived}
                && $record->{level} == $level && $record->{number} == $number;
    }

    return undef;
}

sub remove_song_record {
    my ($records, $wanted) = @_;

    my @kept;
    my $removed = 0;

    for my $record (@$records) {
        my $same_song_id = defined($record->{song_id})
            && defined($wanted->{song_id})
            && $record->{song_id} eq $wanted->{song_id};

        if (!$removed
            && ($same_song_id
                || ($record->{level} == $wanted->{level}
                    && $record->{number} == $wanted->{number}
                    && $record->{title} eq $wanted->{title}))) {
            $removed = 1;
            next;
        }

        push @kept, $record;
    }

    @$records = @kept;
    normalize_song_numbers($records);
    return $removed;
}

sub count_songs_in_level {
    my ($records, $level) = @_;

    my $count = 0;
    for my $record (@$records) {
        $count++ if !$record->{archived} && $record->{level} == $level;
    }

    return $count;
}

sub max_song_line_no {
    my ($records) = @_;

    my $max = 0;
    for my $record (@$records) {
        $max = $record->{line_no} if ($record->{line_no} // 0) > $max;
    }

    return $max;
}

sub insert_song_record {
    my ($records, $level, $position, $title, $line_no, $song_id) = @_;

    # An ordinary Add may not create a second song with the same title. Move
    # supplies an existing song ID and therefore isn't a new song.
    if (!defined($song_id) || $song_id eq '') {
        my $wanted = song_title_identity($title);
        for my $existing (@$records) {
            next unless song_title_identity($existing->{title}) eq $wanted;
            return (0, "Song '$existing->{title}' already exists at level "
                . "$existing->{level} (ID: $existing->{song_id}). "
                . ($existing->{archived}
                    ? "It is archived: use Restore in the song list instead of adding a duplicate."
                    : "Use Move or attach additional media instead of adding it again."));
        }
    }

    $position = count_songs_in_level($records, $level) + 1
        if !defined $position || $position < 1;

    my $max_position = count_songs_in_level($records, $level) + 1;
    $position = $max_position if $position > $max_position;

    for my $record (@$records) {
        next unless $record->{level} == $level;
        $record->{number}++ if $record->{number} >= $position;
    }

    push @$records, {
        level   => 0 + $level,
        number  => 0 + $position,
        title   => $title,
        song_id  => defined($song_id) && length($song_id) ? $song_id : undef,
        archived => 0,
        line_no  => $line_no // (max_song_line_no($records) + 1),
    };

    normalize_song_numbers($records);
    ensure_song_ids($records);
    return (1, undef);
}

sub parse_song_ref {
    my ($input) = @_;
    $input = trim_text($input);

    return (undef, undef, 'Blank song reference.')
        if $input eq '';

    # Accept either "2 3" or "2,3" or "2, 3".
    return (0 + $1, 0 + $2, undef)
        if $input =~ /^(\d+)\s*(?:,|\s+)\s*(\d+)\z/;

    return (
        undef,
        undef,
        'Use level and song number, separated by a space or comma. Example: 2 3 or 2,3.'
    );
}

sub parse_level_and_optional_position {
    my ($input) = @_;
    $input = trim_text($input);

    return (undef, undef, 'Blank level/position.')
        if $input eq '';

    return (0 + $1, undef, undef)
        if $input =~ /^(\d+)\z/;

    return (0 + $1, 0 + $2, undef)
        if $input =~ /^(\d+)\s*(?:,|\s+)\s*(\d+)\z/;

    return (
        undef,
        undef,
        'Use a level, optionally followed by a position. Example: 4 or 4 2 or 4,2.'
    );
}

sub prompt_to_continue {
    my ($message) = @_;
    print "\n$message\n" if defined $message && length $message;
    print "Press Enter to continue...";
    scalar <STDIN>;
}

sub prompt_song_reference {
    my ($prompt, $records) = @_;

    print $prompt;
    chomp(my $input = <STDIN>);

    my ($level, $number, $err) = parse_song_ref($input);
    return (undef, $err) if defined $err;

    if (!valid_song_level($level)) {
        return (undef, "Unknown level $level.");
    }

    my $record = find_song_record($records, $level, $number);
    return (undef, "No song found at level $level, number $number.")
        unless defined $record;

    return ($record, undef);
}

# Attributes are independent of repertoire position. Never use title or
# category+number as a storage key: either may change without changing song ID.
# The TSV is extensible: one song_id + attribute name per row, other future
# attribute names are retained even though this menu currently supports only
# Memorized and Emphasize. The first row is an optional header.
sub read_song_attributes {
    my ($file) = @_;
    $file //= $SONG_ATTRIBUTES_FILE;
    my %attributes;
    return (\%attributes, undef) unless -e $file;

    open my $fh, '<', $file
        or return (undef, "Could not read $file: $!");
    my $line_no = 0;
    while (my $line = <$fh>) {
        $line_no++;
        chomp $line;
        $line =~ s/\r\z//;
        next if $line =~ /^\s*\z/ || $line =~ /^\s*#/;
        my @columns = split /\t/, $line, -1;
        next if $line_no == 1 && @columns == 2
            && $columns[0] eq 'song_id' && $columns[1] eq 'attribute';
        if (@columns != 2 || $columns[0] eq '' || $columns[1] eq ''
            || $columns[0] =~ /[\r\n]/ || $columns[1] =~ /[\r\n]/) {
            close $fh;
            return (undef, "Invalid attribute record at $file line $line_no. No changes made.");
        }
        my ($id, $attribute) = @columns;
        $attribute = 'Memorized' if lc($attribute) eq 'memorized';
        $attribute = 'Emphasize' if lc($attribute) eq 'emphasize';
        $attributes{$id}{$attribute} = 1;
    }
    close $fh;
    return (\%attributes, undef);
}

sub song_has_attribute {
    my ($attributes, $id, $attribute) = @_;
    return !!($attributes->{$id} && $attributes->{$id}{$attribute});
}

sub song_is_memorized {
    my ($attributes, $id) = @_;
    return song_has_attribute($attributes, $id, 'Memorized');
}

sub song_is_emphasized {
    my ($attributes, $id) = @_;
    return song_has_attribute($attributes, $id, 'Emphasize');
}

sub song_attribute_labels {
    my ($attributes, $id) = @_;
    return join(' ', map { "[$_]" }
        grep { song_has_attribute($attributes, $id, $_) } qw(Memorized Emphasize));
}

# Only called after an actual change; preserve the existing file via a backup.
# A failed file read cannot be mistaken for an empty attributes database.
sub write_song_attributes {
    my ($attributes, $file) = @_;
    $file //= $SONG_ATTRIBUTES_FILE;
    my $backup;
    if (-e $file) {
        my $stamp = strftime('%Y%m%d_%H%M%S', localtime(time));
        $backup = "$file.backup-$stamp-$$";
        my $i = 2;
        $backup = "$file.backup-$stamp-$$-" . $i++ while -e $backup;
        return (0, "Cannot back up $file: $!") unless copy($file, $backup);
    }
    my $tmp = "$file.tmp-$$";
    open my $fh, '>', $tmp
        or return (0, "Cannot write temporary attribute file $tmp: $!");
    my $wrote = print {$fh} "song_id\tattribute\n";
    for my $id (sort keys %$attributes) {
        for my $attribute (sort keys %{ $attributes->{$id} }) {
            next unless $attributes->{$id}{$attribute};
            $wrote &&= print {$fh} "$id\t$attribute\n";
        }
    }
    my $closed = close $fh;
    if (!$wrote || !$closed) {
        unlink $tmp;
        return (0, "Could not finish writing attribute file $tmp: $!");
    }
    # Some Windows Perl versions cannot rename over an existing file. The
    # backup allows restoration if either rename or replacement fails.
    if (!rename($tmp, $file)) {
        if (-e $file && unlink($file) && rename($tmp, $file)) {
            # Replaced successfully on Windows.
        }
        else {
            my $err = $!;
            if ($backup && !-e $file) { copy($backup, $file); }
            unlink $tmp;
            return (0, "Could not update $file: $err. "
                . ($backup ? "Backup: $backup" : 'No old file existed.'));
        }
    }
    return (1, "Saved $file." . ($backup ? " Backup: $backup" : ''));
}

# An administrative song lookup: accept a category+number, a permanent song
# ID, or a portion of the title. Archived songs can be selected by ID/title.
sub prompt_attribute_song {
    my ($records) = @_;
    print 'Song (e.g. 2 3, title, or permanent ID; Enter cancels): ';
    my $line = <STDIN>;
    return (undef, 'Canceled.') unless defined $line;
    my $query = trim_text($line);
    return (undef, 'Canceled.') unless length $query;
    if ($query =~ /\A\d+\s*(?:,|\s+)\s*\d+\z/) {
        my ($level, $number, $err) = parse_song_ref($query);
        return (undef, $err) if defined $err;
        my $match = find_song_record($records, $level, $number);
        return ($match, undef) if $match;
        return (undef, "No active song at [$level $number]. Use title or ID for archived songs.");
    }
    my $normalized = normalized_song_search($query);
    my @matches = grep {
        index(normalized_song_search($_->{title}), $normalized) >= 0
            || index(normalized_song_search($_->{song_id} // ''), $normalized) >= 0
    } @$records;
    return (undef, "No songs matched '$query'.") unless @matches;
    if (@matches == 1) { return ($matches[0], undef); }

    @matches = sort {
        $a->{level} <=> $b->{level} || $a->{number} <=> $b->{number}
            || lc($a->{title}) cmp lc($b->{title})
    } @matches;
    print "\nMultiple matches:\n";
    for my $i (0 .. $#matches) {
        printf "%3d. [%s %s] %s (ID: %s)%s\n", $i + 1,
            $matches[$i]{level}, $matches[$i]{number}, $matches[$i]{title},
            $matches[$i]{song_id}, $matches[$i]{archived} ? ' [ARCHIVED]' : '';
    }
    print 'Select 1-' . scalar(@matches) . ' (Enter cancels): ';
    my $answer = <STDIN>;
    return (undef, 'Canceled.') unless defined $answer;
    $answer = trim_text($answer);
    return (undef, 'Canceled.') unless $answer =~ /\A\d+\z/
        && $answer >= 1 && $answer <= @matches;
    return ($matches[$answer - 1], undef);
}

# Run after any successful change to the Memorized attribute (mark or unmark).
# All songs STILL marked Memorized belong in Cold Storage, level 6. The
# reverse is deliberately not automatic: unmarking leaves a song where it is.
# This uses permanent song IDs and preserves each record's attached comments,
# archive flag, media links, and historical practice information.
sub move_memorized_songs_to_cold_storage {
    my ($records, $attributes) = @_;
    my @eligible = sort {
        $a->{level} <=> $b->{level}
            || $a->{number} <=> $b->{number}
            || lc($a->{title}) cmp lc($b->{title})
    } grep {
        song_is_memorized($attributes, $_->{song_id}) && $_->{level} != 6
    } @$records;

    return (1, 'All Memorized songs are already in Cold Storage.', 0)
        unless @eligible;

    # Validate the proposed catalog before touching the real one. Preserve
    # the record objects' metadata, including comment attachments.
    my @updated = map { +{ %$_ } } @$records;
    my %by_id = map { $_->{song_id} => $_ } @updated;
    my $next_number = count_songs_in_level(\@updated, 6);
    for my $original (@eligible) {
        my $song = $by_id{ $original->{song_id} };
        $song->{level} = 6;
        $song->{number} = ++$next_number unless $song->{archived};
    }

    my ($backup, $backup_error) = backup_song_category_file();
    return (0, "Could not move Memorized songs: $backup_error", 0)
        if defined $backup_error;

    my ($ok, $message) = write_song_categories_tsv(\@updated, $SONG_CATEGORY_FILE);
    unless ($ok) {
        # write_song_categories_tsv writes in place: restore from the backup
        # even when the failed write left a partially written catalog.
        my $restored = copy($backup, $SONG_CATEGORY_FILE);
        return (0, "Failed to save Cold Storage moves: $message. "
            . ($restored ? "Original catalog restored from $backup."
                         : "URGENT: could not restore catalog from $backup: $!"), 0);
    }
    @$records = @updated;

    my @events = map {
        my $new = $by_id{ $_->{song_id} };
        +{ action => 'SONG_MOVED', id => $_->{song_id},
            old => "Level $_->{level} position $_->{number}",
            new => "Level 6 position $new->{number}",
            detail => "Automatic: Memorized | $_->{title}" }
    } @eligible;
    my $audit_note = audit_write(@events);
    my $count = scalar @eligible;
    return (1, "Moved $count Memorized song(s) to Cold Storage (level 6). "
        . "Catalog backup: $backup.$audit_note", $count);
}

# A boolean flag is a single attribute row when true and no row when false.
# Edits apply to the song's stable ID; all other attributes are preserved.
sub change_song_attribute {
    my ($records, $attributes, $attribute, $add) = @_;
    die "Unknown supported attribute: $attribute" unless
        $attribute eq 'Memorized' || $attribute eq 'Emphasize';
    my ($record, $err) = prompt_attribute_song($records);
    return $err if defined $err;
    my $id = $record->{song_id};
    my $marked = song_has_attribute($attributes, $id, $attribute);
    return "'$record->{title}' is already $attribute." if $add && $marked;
    return "'$record->{title}' is not marked $attribute." if !$add && !$marked;

    print "\n" . ($add ? 'Mark' : 'Unmark') . " '$record->{title}' "
        . "(ID: $id) as $attribute? [y/N]: ";
    my $answer = <STDIN>;
    return 'No attribute change made.' unless defined($answer)
        && lc(trim_text($answer)) eq 'y';

    if ($add) { $attributes->{$id}{$attribute} = 1; }
    else {
        delete $attributes->{$id}{$attribute};
        delete $attributes->{$id} unless keys %{ $attributes->{$id} };
    }
    my ($ok, $msg) = write_song_attributes($attributes);
    if (!$ok) {
        # Do not leave the menu's memory out of sync with the disk on failure.
        if ($add) {
            delete $attributes->{$id}{$attribute};
            delete $attributes->{$id} unless keys %{ $attributes->{$id} };
        }
        else { $attributes->{$id}{$attribute} = 1; }
        return $msg;
    }
    my $cold_storage_message = '';
    if ($attribute eq 'Memorized') {
        my ($moved_ok, $moved_message) =
            move_memorized_songs_to_cold_storage($records, $attributes);
        unless ($moved_ok) {
            # The catalog could not be made consistent. Revert this attribute
            # change, including on disk, rather than claim it was completed.
            if ($add) {
                delete $attributes->{$id}{$attribute};
                delete $attributes->{$id} unless keys %{ $attributes->{$id} };
            }
            else { $attributes->{$id}{$attribute} = 1; }
            my ($restored, $restore_message) = write_song_attributes($attributes);
            return "Memorized change NOT completed. $moved_message "
                . ($restored ? 'Attribute change rolled back.'
                             : "URGENT: attribute rollback failed: $restore_message");
        }
        $cold_storage_message = " $moved_message";
    }
    my $audit_note = audit_write({
        action => $add ? 'ATTRIBUTE_SET' : 'ATTRIBUTE_REMOVED',
        id => $id, old => $add ? 'No' : 'Yes',
        new => $add ? 'Yes' : 'No', detail => "$attribute | $record->{title}",
    });
    return ($add ? 'Marked' : 'Unmarked') . " '$record->{title}' as $attribute. $msg$cold_storage_message$audit_note";
}

# Retained as an alias for older callers or test harnesses.
sub change_memorized_attribute {
    my ($records, $attributes, $add) = @_;
    return change_song_attribute($records, $attributes, 'Memorized', $add);
}

# Return the most recent *credited* practice event for selected song IDs.
# Session rows are cumulative: the latest snapshot per (session, song_id)
# replaces older snapshots. Invalid/orphan sessions are excluded. A zero
# snapshot from an undo/deletion is not evidence of a practice event.
# Manual adjustments are dated, and only a net positive total on that date
# is treated as ad-hoc practice. A subtraction alone never refreshes a song.
sub memorized_last_practice_by_id {
    my ($wanted_ids) = @_;
    my %last;
    return \%last unless %$wanted_ids;

    my $valid = valid_logged_sessions();
    my ($snapshots) = read_song_log_for_report($SONG_LOG_FILE, $valid);
    for my $snapshot (values %$snapshots) {
        my $id = $snapshot->{id};
        next unless $wanted_ids->{$id} && ($snapshot->{seconds} // 0) > 0;
        # The current session's live data replaces its saved snapshot; an
        # undo after Save must not leave an old 'last practiced' behind.
        next if defined($session_start_stamp)
            && $snapshot->{session} eq $session_start_stamp;
        my $stamp = $snapshot->{last} // '';
        my $precise = 1;
        if (!length($stamp)) {
            # Old session logs may lack the last_practiced_at column.
            $stamp = $snapshot->{saved} // '';
            $precise = 0;
        }
        my ($epoch) = parse_log_stamp($stamp);
        next unless defined $epoch;
        if (!exists($last{$id}) || $epoch > $last{$id}{epoch}) {
            $last{$id} = {
                epoch => $epoch, text => $stamp,
                source => $precise ? 'timer' : 'saved estimate',
            };
        }
    }

    my ($adjustments) = read_song_adjustment_log($SONG_ADJUST_FILE);
    my %net_by_day;
    for my $entry (@$adjustments) {
        next unless $wanted_ids->{ $entry->{id} };
        $net_by_day{ $entry->{id} . "\0" . $entry->{date} } += $entry->{seconds};
    }
    for my $key (keys %net_by_day) {
        next unless $net_by_day{$key} > 0.01;
        my ($id, $date) = split /\0/, $key, 2;
        my ($epoch) = parse_log_stamp("$date 00:00:00");
        next unless defined $epoch;
        if (!exists($last{$id}) || $epoch > $last{$id}{epoch}) {
            $last{$id} = {
                epoch => $epoch, text => $date,
                source => 'dated manual practice',
            };
        }
    }

    # The current session may not yet have been saved to the TSV files.
    # Its in-memory data takes precedence over the current session's disk
    # snapshot (which is skipped above to avoid a stale last-played time).
    for my $id (keys %$wanted_ids) {
        my $epoch = $song_last_practiced_epoch{$id} // 0;
        next unless ($song_elapsed{$id} // 0) > 0 && $epoch > 0;
        if (!exists($last{$id}) || $epoch > $last{$id}{epoch}) {
            $last{$id} = {
                epoch => $epoch, text => fmt_stamp($epoch), source => 'timer',
            };
        }
    }
    return \%last;
}

# Memory reviews are provisional reminders based on *practice recency*.
# Actual successful recall is not yet tracked separately. Archived songs
# remain in the report, but do not trigger prompts on the main screen.
sub memorized_review_status_by_id {
    my ($records, $attributes, $now_epoch) = @_;
    $now_epoch //= time;
    my %wanted = map { $_->{song_id} => 1 }
        songs_with_attribute($records, $attributes, 'Memorized');
    my $last = memorized_last_practice_by_id(\%wanted);
    my %statuses;
    for my $id (keys %wanted) {
        my $entry = $last->{$id};
        my $age = $entry ? $now_epoch - $entry->{epoch} : undef;
        $age = 0 if defined($age) && $age < 0;
        $statuses{$id} = {
            last => $entry,
            days_since => defined($age) ? int($age / 86400) : undef,
            due => !$entry || $age >= $MEMORIZED_REVIEW_INTERVAL_DAYS * 86400,
        };
    }
    return \%statuses;
}

sub memorized_review_due_count {
    my ($records, $attributes) = @_;
    my $statuses = memorized_review_status_by_id($records, $attributes);
    return scalar grep {
        !($_->{archived} // 0)
            && ($statuses->{$_->{song_id}}{due} // 0)
    } songs_with_attribute($records, $attributes, 'Memorized');
}

# One ordering shared by the saved report and the on-screen practice menu.
# Keep archived entries visible for historical reference, but do not let an
# archived song start practice until it has been restored to the repertoire.
sub songs_with_attribute {
    my ($records, $attributes, $attribute) = @_;
    die "Unknown supported attribute: $attribute" unless
        $attribute eq 'Memorized' || $attribute eq 'Emphasize';
    return sort {
        $a->{level} <=> $b->{level}
            || ($a->{archived} // 0) <=> ($b->{archived} // 0)
            || $a->{number} <=> $b->{number}
            || lc($a->{title}) cmp lc($b->{title})
    } grep { song_has_attribute($attributes, $_->{song_id}, $attribute) } @$records;
}

sub song_attribute_report_text {
    my ($records, $attributes, $attribute) = @_;
    my @songs = songs_with_attribute($records, $attributes, $attribute);
    my $review = $attribute eq 'Memorized'
        ? memorized_review_status_by_id($records, $attributes)
        : {};
    my $upper = uc $attribute;
    my $out = "SONGS WITH ATTRIBUTE: $upper\n";
    $out .= '=' x (22 + length($upper)) . "\n";
    $out .= 'Generated: ' . fmt_stamp(time) . "\n";
    $out .= 'Total: ' . scalar(@songs) . "\n";
    if ($attribute eq 'Memorized') {
        my $due_count = scalar grep {
            !($_->{archived} // 0)
                && ($review->{$_->{song_id}}{due} // 0)
        } @songs;
        $out .= "Memory checks due: $due_count active song(s)\n";
        $out .= "Review interval: $MEMORIZED_REVIEW_INTERVAL_DAYS days since last credited practice\n";
    }
    $out .= "\n";
    if (!@songs) { $out .= "No songs have the $attribute attribute yet.\n"; }
    my $last_level;
    for my $i (0 .. $#songs) {
        my $song = $songs[$i];
        if (!defined($last_level) || $last_level != $song->{level}) {
            $last_level = $song->{level};
            # Attribute reports show the category name without its numeric
            # level. Keep the actual level/position internally for lookups.
            my $option = option_for_level($last_level);
            my $heading = $option ? $option->{name} : 'Other';
            $out .= $heading . "\n";
            $out .= '-' x length($heading) . "\n";
        }
        # The sequential selection number is sufficient here. Song ID,
        # category level and within-category position remain internal.
        $out .= sprintf("%3d. %s%s\n",
            $i + 1, $song->{title},
            $song->{archived} ? ' [ARCHIVED]' : '');
        if ($attribute eq 'Memorized') {
            my $status = $review->{$song->{song_id}};
            my $last = $status->{last};
            if ($last) {
                $out .= "      Last practiced: $last->{text}";
                $out .= ' [approximate]' if $last->{source} eq 'saved estimate';
                $out .= ' [manual entry]' if $last->{source} eq 'dated manual practice';
                $out .= " | $status->{days_since} day(s) ago\n";
            }
            else {
                $out .= "      Last practiced: Not recorded\n";
            }
            my $label = $song->{archived} ? 'ARCHIVED (not scheduled)'
                      : $status->{due} ? 'DUE - test from memory'
                      : 'Not yet due';
            $out .= "      Memory check: $label\n";
        }
    }
    $out .= "\nArchive status does not remove an attribute or its historical data.\n";
    if ($attribute eq 'Memorized') {
        $out .= "Practice recency is only a reminder; successfully recalling the song is not yet tracked.\n";
        $out .= "Old logs without a last-practiced timestamp use the session save time as an estimate.\n";
    }
    return $out;
}

sub memorized_song_report_text {
    my ($records, $attributes) = @_;
    return song_attribute_report_text($records, $attributes, 'Memorized');
}

sub generate_song_attribute_report {
    my ($records, $attributes, $attribute) = @_;
    my $file = $attribute eq 'Memorized' ? $MEMORIZED_REPORT_FILE
             : $attribute eq 'Emphasize' ? $EMPHASIZE_REPORT_FILE
             : die "Unknown attribute $attribute";
    my $out = song_attribute_report_text($records, $attributes, $attribute);
    print_paged_song_categories($out);
    if (open my $fh, '>', $file) {
        my $ok = print {$fh} $out;
        my $closed = close $fh;
        $ok = $ok && $closed;
        return $ok
            ? "Report displayed and saved to $file."
            : "Report displayed, but could not finish writing $file: $!";
    }
    return "Report displayed, but could not save $file: $!";
}

# Show an attribute report, then optionally practice one of its songs.
# The displayed serial is stable within this report; alternatively accept the
# familiar "level number" reference. Return (started, message) to let nested
# Attributes/Category menus close all the way back to the main practice screen.
# No selection is changed if the user presses Enter or provides an invalid ID.
sub offer_practice_from_attribute_report {
    my ($records, $attributes, $attribute) = @_;
    my @songs = songs_with_attribute($records, $attributes, $attribute);
    my $report_message = generate_song_attribute_report($records, $attributes, $attribute);
    print "\n$report_message\n";
    if (!@songs) {
        print "Press Enter to return...";
        scalar <STDIN>;
        return (0, $report_message);
    }

    while (1) {
        print "\nPractice a song (1-" . scalar(@songs)
            . "; Enter returns): ";
        my $line = <STDIN>;
        return (0, $report_message) unless defined $line;
        my $input = trim_text($line);
        return (0, $report_message) if $input eq '';

        my $song;
        if ($input =~ /\A\d+\z/) {
            my $choice = 0 + $input;
            if ($choice >= 1 && $choice <= @songs) {
                $song = $songs[$choice - 1];
            }
        }
        elsif ($input =~ /\A(\d+)\s*(?:,|\s+)\s*(\d+)\z/) {
            my ($level, $number) = ($1, $2);
            ($song) = grep { $_->{level} == $level && $_->{number} == $number
                && !$_->{archived} } @songs;
            if (!$song) {
                print "No active song in this report at [$level $number].\n";
                next;
            }
        }
        if (!$song) {
            print "Not a listed song. Enter its report number or press Enter.\n";
            next;
        }
        if ($song->{archived}) {
            print "'$song->{title}' is archived. Restore it from Song Categories before practicing it.\n";
            next;
        }

        # Same pathway as Find and category selections, including the
        # default-None / All / Some attached-media prompt and one-minute rule.
        my ($started, $message) = start_practicing_song_record($song);
        return (1, $message) if $started;
        print "$message\n";
    }
}

# F10 opens the same Emphasize report available from Song Categories ->
# Attributes -> p. It reads current TSV files and does not change song data.
# The caller has already stopped the live timing segment. Restore console
# line input for the report pager, then return to cbreak mode afterward.
sub show_emphasize_report_hotkey {
    ReadMode('restore');
    my ($records, $warnings) = read_song_categories_tsv($SONG_CATEGORY_FILE);
    if (!defined $records) {
        prompt_to_continue(join("\n", @$warnings));
        ReadMode('cbreak');
        $last_tick = time;
        return 'Could not load song catalog for Emphasize report.';
    }
    my ($attributes, $err) = read_song_attributes();
    if (defined $err) {
        prompt_to_continue($err);
        ReadMode('cbreak');
        $last_tick = time;
        return 'Could not read song attributes for Emphasize report.';
    }
    my ($started, $message) = offer_practice_from_attribute_report(
        $records, $attributes, 'Emphasize');
    ReadMode('cbreak');
    $last_tick = time;
    return $message;
}

sub generate_memorized_report {
    my ($records, $attributes) = @_;
    return generate_song_attribute_report($records, $attributes, 'Memorized');
}

# The Attributes menu can be reached through Song Categories (c -> t)
# or directly from the main screen (F8). The return label follows the caller.
sub manage_song_attributes {
    my ($records, $return_to) = @_;
    $return_to //= 'Song Categories';
    my $message = '';
    while (1) {
        my ($attributes, $err) = read_song_attributes();
        return $err if defined $err;
        clear_screen();
        my $memorized_count = scalar grep {
            song_is_memorized($attributes, $_->{song_id})
        } @$records;
        my $emphasize_count = scalar grep {
            song_is_emphasized($attributes, $_->{song_id})
        } @$records;
        print "SONG ATTRIBUTES\n===============\n\n";
        print "Supported attributes: Memorized, Emphasize\n";
        print "Memorized: $memorized_count song(s); Emphasize: $emphasize_count song(s)\n";
        print "Storage: $SONG_ATTRIBUTES_FILE (permanent song IDs)\n";
        print "Marking/Unmarking Memorized checks all marked songs and moves them to Cold Storage (6).\n";
        print "Unmarking does not move a song back to another level.\n\n";
        print "m = Mark Memorized       u = Unmark Memorized       r = Memorized report\n";
        print "e = Mark Emphasize       x = Unmark Emphasize       p = Emphasize report\n";
        print "Enter = Return to $return_to\n\n";
        print "Message: $message\n\n" if length $message;
        print 'Attributes action: ';
        my $input = <STDIN>;
        last unless defined $input;
        my $choice = lc trim_text($input);
        last if $choice eq '';
        if ($choice eq 'm') { $message = change_song_attribute($records, $attributes, 'Memorized', 1); }
        elsif ($choice eq 'u') { $message = change_song_attribute($records, $attributes, 'Memorized', 0); }
        elsif ($choice eq 'e') { $message = change_song_attribute($records, $attributes, 'Emphasize', 1); }
        elsif ($choice eq 'x') { $message = change_song_attribute($records, $attributes, 'Emphasize', 0); }
        elsif ($choice eq 'r' || $choice eq 'p') {
            my ($started, $report_message) = offer_practice_from_attribute_report(
                $records, $attributes, $choice eq 'r' ? 'Memorized' : 'Emphasize');
            return ($report_message, 1) if $started;
            $message = $report_message;
        }
        else { $message = "Unknown Attributes action '$choice'."; }
    }
    return 'Returned from Attributes.';
}

# F8 opens the Attributes submenu directly from the main timer, bypassing
# Song Categories. This is the very same menu and report selection logic
# as c -> t; timing is suspended by the main loop while it is open.
sub show_attributes_hotkey {
    ReadMode('restore');
    my ($records, $warnings, $ids_changed) =
        read_song_categories_tsv($SONG_CATEGORY_FILE);
    if (!defined $records) {
        prompt_to_continue(join("\n", @$warnings));
        ReadMode('cbreak');
        $last_tick = time;
        return 'Could not load song catalog for Attributes.';
    }

    # Match the category editor's legacy-ID upgrade so attributes keep
    # pointing at stable IDs even if the catalog contains old-style rows.
    if ($ids_changed) {
        my ($ok, $message) = write_song_categories_tsv(
            $records, $SONG_CATEGORY_FILE);
        unless ($ok) {
            prompt_to_continue($message);
            ReadMode('cbreak');
            $last_tick = time;
            return 'Could not assign permanent song IDs for Attributes.';
        }
    }

    my ($message, $practice_started) =
        manage_song_attributes($records, 'Timer');
    ReadMode('cbreak');
    $last_tick = time;
    return $message;
}

# Resolve song and activity media without inventing repertoire songs.
# Theory, Scales, and Ear training each have independent attachments;
# all three remain available through Media/Audacity while temporarily paused.
sub current_material_owner {
    return ($current_song_id, $current_song_title) if length $current_song_id;
    my ($id, $title) = media_category_owner($current_key);
    return ($id, $title) if defined $id;
    if ($current_key eq pause_key() && length $resume_key) {
        return ($resume_song_id, $resume_song_title) if length $resume_song_id;
        return media_category_owner($resume_key);
    }
    return (undef, undef);
}

# This is used only by the sheet-music management menu. Other song selectors
# still require a real level/number; neither supplemental category is a song.
sub prompt_attachment_reference {
    my ($prompt, $records) = @_;
    print $prompt;
    my $input = <STDIN>;
    return (undef, 'Canceled.') unless defined $input;
    chomp $input;
    $input = trim_text($input);

    if (lc($input) eq 'scales') {
        return ({
            title => 'Scales', song_id => $SCALES_ATTACHMENT_ID,
            is_scales_attachment => 1,
        }, undef);
    }
    if (lc($input) eq 'ear' || lc($input) eq 'ear training') {
        return ({
            title => 'Ear training', song_id => $EAR_TRAINING_ATTACHMENT_ID,
            is_ear_training_attachment => 1,
        }, undef);
    }
    if (lc($input) eq 'theory') {
        return ({
            title => 'Theory', song_id => $THEORY_ATTACHMENT_ID,
            is_theory_attachment => 1,
        }, undef);
    }

    my ($level, $number, $err) = parse_song_ref($input);
    return (undef, $err) if defined $err;
    return (undef, "Unknown level $level.") unless valid_song_level($level);
    my $record = find_song_record($records, $level, $number);
    return (undef, "No song found at level $level, number $number.")
        unless defined $record;
    return ($record, undef);
}

sub read_sheet_music_tsv {
    my ($file) = @_;
    $file //= $SHEET_MUSIC_FILE;

    return ([], []) unless -e $file;

    open my $fh, '<', $file
        or return ([], ["Could not read $file: $!"]);

    my @records;
    my @warnings;
    my $line_no = 0;

    while (my $line = <$fh>) {
        $line_no++;
        chomp $line;
        $line =~ s/\r\z//;
        next if $line =~ /^\s*\z/;

        my ($song_id, $target) = split /\t/, $line, 2;
        $song_id = trim_text($song_id);
        $target  = trim_text($target);

        if ($song_id eq '' || $target eq '') {
            push @warnings, "Sheet music line $line_no ignored: expected song_id<TAB>path_or_link.";
            next;
        }

        push @records, {
            song_id => $song_id,
            target  => $target,
            line_no => $line_no,
        };
    }

    close $fh;
    return (\@records, \@warnings);
}

sub max_sheet_music_line_no {
    my ($records) = @_;

    my $max = 0;
    for my $record (@$records) {
        $max = $record->{line_no} if ($record->{line_no} // 0) > $max;
    }

    return $max;
}

sub write_sheet_music_tsv {
    my ($records, $file) = @_;
    $file //= $SHEET_MUSIC_FILE;

    my ($previous, $read_warnings) = read_sheet_music_tsv($file);
    return (0, join('; ', @$read_warnings)) if @$read_warnings;
    open my $fh, '>', $file
        or return (0, "Could not write $file: $!");

    for my $record (sort {
        $a->{song_id} cmp $b->{song_id}
            || ($a->{line_no} // 0) <=> ($b->{line_no} // 0)
            || $a->{target} cmp $b->{target}
    } @$records) {
        next unless defined($record->{song_id}) && length($record->{song_id});
        next unless defined($record->{target})  && length($record->{target});

        print $fh join("\t", $record->{song_id}, $record->{target}), "\n";
    }

    close $fh or return (0, "Could not close $file: $!");
    my $audit_note = audit_sheet_changes($previous, $records);
    return (1, "Saved sheet music links to $file.$audit_note");
}

sub sheet_music_for_song {
    my ($sheet_records, $song_id) = @_;
    return () unless defined $song_id;

    return sort {
        ($a->{line_no} // 0) <=> ($b->{line_no} // 0)
            || $a->{target} cmp $b->{target}
    } grep { ($_->{song_id} // '') eq $song_id } @$sheet_records;
}

sub sheet_music_count_by_song_id {
    my ($sheet_records) = @_;

    my %count;
    for my $record (@$sheet_records) {
        $count{ $record->{song_id} }++ if defined $record->{song_id};
    }

    return \%count;
}

sub remove_sheet_music_for_song_id {
    my ($sheet_records, $song_id) = @_;

    my @kept;
    my $removed = 0;

    for my $record (@$sheet_records) {
        if (defined($song_id) && ($record->{song_id} // '') eq $song_id) {
            $removed++;
            next;
        }

        push @kept, $record;
    }

    @$sheet_records = @kept;
    return $removed;
}

sub add_sheet_music_record {
    my ($sheet_records, $song_id, $target) = @_;

    push @$sheet_records, {
        song_id => $song_id,
        target  => $target,
        line_no => max_sheet_music_line_no($sheet_records) + 1,
    };
}

sub delete_one_sheet_music_record {
    my ($sheet_records, $wanted) = @_;

    my @kept;
    my $removed = 0;

    for my $record (@$sheet_records) {
        if (!$removed
            && ($record->{song_id} // '') eq ($wanted->{song_id} // '')
            && ($record->{target}  // '') eq ($wanted->{target}  // '')
            && (($record->{line_no} // 0) == ($wanted->{line_no} // 0))) {
            $removed = 1;
            next;
        }

        push @kept, $record;
    }

    @$sheet_records = @kept;
    return $removed;
}

sub open_sheet_music_target {
    my ($target) = @_;

    return "Nothing to open." unless defined $target && length $target;

    my $rc;
    if ($^O eq 'MSWin32') {
        # Sheet music supports arbitrary targets and URLs, but local TXT files
        # always open in Notepad and JPG/PNG images in IrfanView, regardless of
        # Windows file associations. The Vim activity report is separate.
        if ($target =~ /\.(?:txt|jpe?g|png)\z/i && $target !~ m{^[a-z][a-z0-9+.-]*://}i) {
            return open_one_song_material($target);
        }
        $rc = system('cmd', '/c', 'start', '', $target);
    }
    elsif ($^O eq 'darwin') {
        $rc = system('open', $target);
    }
    else {
        $rc = system('xdg-open', $target);
    }

    return $rc == 0
        ? "Opened: $target"
        : "Tried to open '$target', but the operating system command returned $rc.";
}

sub prompt_sheet_music_number {
    my ($prompt, @items) = @_;

    return (undef, 'No sheet music is attached to this song.') unless @items;

    print $prompt;
    chomp(my $input = <STDIN>);
    $input = trim_text($input);

    return (undef, 'Canceled.') if $input eq '';
    return (undef, 'Use the displayed sheet-music number.') unless $input =~ /^\d+\z/;

    my $idx = $input - 1;
    return (undef, "No sheet-music entry number $input.")
        if $idx < 0 || $idx > $#items;

    return ($items[$idx], undef);
}

sub manage_sheet_music_for_song {
    my ($records) = @_;

    # Persist generated IDs before storing sheet music against them.
    my ($cat_ok, $cat_msg) = write_song_categories_tsv($records, $SONG_CATEGORY_FILE);
    return $cat_msg unless $cat_ok;

    my ($record, $err) = prompt_attachment_reference(
        "Song (level number, e.g. 2 3), 'scales', 'ear', or 'theory': ",
        $records,
    );

    return $err if defined $err;

    my ($sheet_records, $sheet_warnings) = read_sheet_music_tsv($SHEET_MUSIC_FILE);
    my $message = '';

    while (1) {
        clear_screen();

        print "Sheet Music
";
        print "===========

";
        if ($record->{is_scales_attachment} || $record->{is_ear_training_attachment} || $record->{is_theory_attachment}) {
            print "Practice: $record->{title} (category, not a song)\n";
        }
        else {
            print "Song: [$record->{level} $record->{number}] $record->{title}\n";
        }
        print "Song ID: $record->{song_id}
";
        print "Source: $SHEET_MUSIC_FILE
";
        print "Format: song_id<TAB>path_or_link
";
        print "Example: G:\\My Drive\\tab\\this example tab.pdf
";
        print "PDF, TXT, ODT, JPG, PNG, URLs, and arbitrary system files are allowed.
";
        print "Local JPG/PNG images open in IrfanView.

";

        my @items = sheet_music_for_song($sheet_records, $record->{song_id});

        if (@items) {
            print "Attached sheet music:
";
            my $n = 1;
            for my $item (@items) {
                print sprintf("%3d. %s
", $n, $item->{target});
                $n++;
            }
        }
        else {
            print "No sheet music attached to this song yet.
";
        }

        if (@$sheet_warnings) {
            print "
Warnings
";
            print "--------
";
            for my $warning (@$sheet_warnings) {
                print "$warning
";
            }
        }

        print "
Message: $message
" if length $message;
        print "
Sheet music actions: a = add   d = delete   o = open   Enter = return
";
        print "Choose sheet music action: ";
        chomp(my $choice = <STDIN>);
        $choice = lc trim_text($choice);

        if ($choice eq '') {
            last;
        }
        elsif ($choice eq 'a') {
            print "Path/link to add, or Enter to cancel: ";
            chomp(my $target = <STDIN>);
            $target = trim_text($target);

            if ($target eq '') {
                $message = 'Add canceled.';
            }
            elsif ($target =~ /\t/) {
                $message = 'Add canceled: paths/links may not contain tabs.';
            }
            else {
                add_sheet_music_record($sheet_records, $record->{song_id}, $target);
                my ($ok, $msg) = write_sheet_music_tsv($sheet_records, $SHEET_MUSIC_FILE);
                $message = $ok ? "Added sheet music. $msg" : $msg;
            }
        }
        elsif ($choice eq 'd') {
            my ($item, $item_err) = prompt_sheet_music_number(
                "Sheet music number to delete, or Enter to cancel: ",
                @items,
            );

            if (defined $item_err) {
                $message = $item_err;
            }
            else {
                print "Delete '$item->{target}'? Type y to confirm: ";
                chomp(my $confirm = <STDIN>);

                if (lc(trim_text($confirm)) eq 'y') {
                    my $deleted = delete_one_sheet_music_record($sheet_records, $item);
                    my ($ok, $msg) = write_sheet_music_tsv($sheet_records, $SHEET_MUSIC_FILE);
                    $message = $deleted
                        ? ($ok ? "Deleted sheet music. $msg" : $msg)
                        : 'No matching sheet music entry was deleted.';
                }
                else {
                    $message = 'Delete canceled.';
                }
            }
        }
        elsif ($choice eq 'o') {
            my ($item, $item_err) = prompt_sheet_music_number(
                "Sheet music number to open, or Enter to cancel: ",
                @items,
            );

            $message = defined $item_err
                ? $item_err
                : open_sheet_music_target($item->{target});
        }
        else {
            $message = "Unknown sheet music option '$choice'. Use a, d, o, or Enter.";
        }
    }

    return length($message) ? $message : "Returned from sheet music editor.";
}

sub song_category_action_legend {
    return join(
        "\n",
        "Category actions",
        "----------------",
        "p = practice   f(y) = find   s = sheet music   t = Attributes   d = archive (hide)   x = DELETE song   u = restore archived   a = add   m = move/search   n = rename   l = audit log",
        "Press Enter without a command to return to the timer.",
        "Song references use level and song number (2 3 or 2,3); Move also accepts a title/ID search.",
        "Archive hides a song from normal lists, practice Find, tips, and Adjust; category Find can locate it.",
        "Restoring an archived song uses its ORIGINAL song_id and appends it to its former level.",
        "Switching directly to a category, Scales, Ear training, Theory, or Pause stops the song clock.",
        "",
    );
}

sub format_song_categories {
    my ($records, $warnings, $sheet_records) = @_;
    $records       //= [];
    $warnings      //= [];
    $sheet_records //= [];

    my $by_level = group_song_categories_by_level($records);
    my @levels = sort { $a <=> $b } keys %$by_level;
    my ($attributes, $attr_error) = read_song_attributes();
    $attributes //= {};

    my $out = '';
    $out .= "Song Categories\n";
    $out .= "===============\n\n";
    $out .= "Source: $SONG_CATEGORY_FILE\n";
    $out .= "Format: level<TAB>number<TAB>song title<TAB>song_id[<TAB>archived]\n";
    $out .= "Song reference format: level number, e.g. 2 3 or 2,3\n";
    $out .= "Sheet music source: $SHEET_MUSIC_FILE\n\n";

    if (!@levels) {
        $out .= "No active songs in the repertoire. Archived songs can be restored with u.\n\n";
    }
    else {
        for my $level (@levels) {
            $out .= level_label($level) . "\n";
            $out .= '-' x length(level_label($level)) . "\n";

            my $sheet_counts = sheet_music_count_by_song_id($sheet_records);

            for my $record (@{ $by_level->{$level} }) {
                my $sheet_count = $sheet_counts->{ $record->{song_id} } // 0;
                my $sheet_label = $sheet_count == 1
                    ? ' [1 sheet file]'
                    : $sheet_count > 1
                        ? " [$sheet_count sheet files]"
                        : '';

                my $marks = song_attribute_labels($attributes, $record->{song_id});
                $marks = " $marks" if length $marks;
                $out .= sprintf("%3d. %s%s%s\n", $record->{number}, $record->{title}, $marks, $sheet_label);
            }

            $out .= "\n";
        }
    }

    # Keep the edit legend attached to the rendered song list itself, so it
    # always appears immediately after the songs rather than being separated
    # from the list by later prompt logic.
    $out .= song_category_action_legend();

    if (defined $attr_error) {
        $out .= "Attribute warning: $attr_error\n\n";
    }

    if (@$warnings) {
        $out .= "Warnings\n";
        $out .= "--------\n";
        for my $warning (@$warnings) {
            $out .= "$warning\n";
        }
        $out .= "\n";
    }

    return $out;
}

# Print the fully formatted category/song listing in screen-sized pages.
# A continuation key is consumed here, so it cannot be mistaken for an
# editing command when the action prompt appears on the last page.
sub print_paged_song_categories {
    my ($output) = @_;
    my $page_size = 33;

    my @lines = split /\n/, $output;
    my $total = scalar @lines;

    for (my $offset = 0; $offset < $total; $offset += $page_size) {
        clear_screen();

        my $last = $offset + $page_size - 1;
        $last = $total - 1 if $last >= $total;
        print join("\n", @lines[$offset .. $last]), "\n";

        if ($last < $total - 1) {
            print "\nPress any key to list more...";
            ReadMode('cbreak');
            ReadKey(0);
            ReadMode('restore');
        }
    }
}

# A reversible archive never deletes the song row, the stable song_id, or
# anything in historical practice, media, sheet-music, or adjustment TSVs.
# Keep a copy of the catalog before updating its archive flags.
sub backup_song_category_file {
    my $file = $SONG_CATEGORY_FILE;
    return (undef, "Catalog not found: $file") unless -f $file;
    my $stamp = strftime('%Y%m%d_%H%M%S', localtime(time));
    my $backup = "$file.archive-backup-$stamp-$$.bak";
    my $serial = 2;
    while (-e $backup) {
        $backup = "$file.archive-backup-$stamp-$$-$serial.bak";
        $serial++;
    }
    return (undef, "Could not back up $file: $!") unless copy($file, $backup);
    return ($backup, undef);
}

# Permanently remove a repertoire catalog entry. This is distinct from Archive:
# the TSV row disappears, but historical practice, audit, attachment TSV data,
# and physical media files are NEVER erased. Require typing the exact song ID
# and back up the catalog before changing it.
sub delete_song_category_entry {
    my ($records) = @_;
    print "\nDELETE SONG FROM CATALOG\n";
    print "------------------------\n";
    print "Enter song title, ID, or level and number (e.g. 2 3).\n";
    print "Song to delete (Enter cancels): ";
    my $input = <STDIN>;
    return 'Delete canceled.' unless defined $input;
    my $query = trim_text($input);
    return 'Delete canceled.' if $query eq '';

    my @matches;
    if ($query =~ /^\d+\s*(?:,|\s+)\s*\d+\z/) {
        my ($level, $number, $err) = parse_song_ref($query);
        return $err if defined $err;
        my $record = find_song_record($records, $level, $number);
        return "No active song found at [$level $number]." unless $record;
        @matches = ($record);
    }
    else {
        @matches = find_category_song_matches($records, $query);
    }
    return "No song matching '$query' in the catalog." unless @matches;

    my $record;
    if (@matches == 1) {
        $record = $matches[0];
    }
    else {
        print "\nMatching songs:\n";
        for my $i (0 .. $#matches) {
            printf "  %d. [%d %d] %s (ID: %s)%s\n", $i + 1,
                $matches[$i]{level}, $matches[$i]{number},
                $matches[$i]{title}, $matches[$i]{song_id},
                $matches[$i]{archived} ? ' [archived]' : '';
        }
        print "Choose song (1-" . scalar(@matches) . "; Enter cancels): ";
        my $answer = <STDIN>;
        return 'Delete canceled.' unless defined $answer;
        $answer = trim_text($answer);
        return 'Delete canceled.' if $answer eq '';
        return "Invalid selection '$answer'. No changes made."
            unless $answer =~ /^\d+\z/ && $answer >= 1 && $answer <= @matches;
        $record = $matches[$answer - 1];
    }

    my $id = $record->{song_id};
    my $title = $record->{title};
    print "\nDELETE '$title' (ID: $id) FROM THE SONG CATALOG?\n";
    print "The entry will disappear from lists and searches.\n";
    print "Historical practice logs, media references, and actual files will NOT be deleted.\n";
    print "A backup of $SONG_CATEGORY_FILE will be created.\n";
    print "Type the exact song ID '$id' to confirm (Enter cancels): ";
    my $confirm = <STDIN>;
    return 'Delete canceled.' unless defined $confirm;
    return 'Delete canceled; no changes made.' if trim_text($confirm) ne $id;

    my ($backup, $backup_err) = backup_song_category_file();
    return "Delete failed: $backup_err" if defined $backup_err;

    my @updated = map { +{ %$_ } } @$records;
    return "Delete failed; song ID not found. Catalog backup: $backup."
        unless remove_song_record(\@updated, $record);
    my ($ok, $msg) = write_song_categories_tsv(\@updated, $SONG_CATEGORY_FILE);
    return "Delete failed; catalog backup: $backup. $msg" unless $ok;

    my ($check) = read_song_categories_tsv($SONG_CATEGORY_FILE);
    return "Catalog was saved but deletion could not be verified. Backup: $backup."
        unless defined($check) && !grep { ($_->{song_id} // '') eq $id } @$check;

    if ($current_song_id eq $id) {
        $current_key = pause_key();
        clear_current_song();
    }
    clear_resume_selection() if $resume_song_id eq $id;
    $displayed_tip_song_id = '' if $displayed_tip_song_id eq $id;

    my $audit_note = audit_write({ action => 'SONG_DELETED',
        id => $id, old => "Level $record->{level} position $record->{number}",
        new => 'removed from song catalog', detail => $title });
    return "DELETED '$title' (ID: $id) from the catalog. "
        . "History and media references retained. Backup: $backup.$audit_note";
}

sub archive_song_category_entry {
    my ($records) = @_;
    my ($record, $err) = prompt_song_reference(
        "Song to archive (level and number, e.g. 2 3): ", $records,
    );
    return $err if defined $err;

    print "\nArchive [$record->{level} $record->{number}] $record->{title} "
        . "(ID: $record->{song_id})?\n";
    print "Its practice history and all media attachments will be KEPT.\n";
    print "It will be hidden from the repertoire, Find, Adjust, and practice tips.\n";
    print "Type y to confirm [y/N]: ";
    my $confirm = <STDIN>;
    return 'Archive canceled.' unless defined($confirm) && lc(trim_text($confirm)) eq 'y';

    my ($backup, $backup_err) = backup_song_category_file();
    return $backup_err if defined $backup_err;

    $record->{archived} = 1;
    my ($ok, $msg) = write_song_categories_tsv($records, $SONG_CATEGORY_FILE);
    if (!$ok) {
        $record->{archived} = 0;
        return "Archive failed; catalog backup: $backup. $msg";
    }

    # If the song is being practiced or is suspended by Pause, prevent it
    # from remaining selected after it is hidden. Existing credited seconds,
    # selection history, and session timeline segments are NOT removed.
    if ($current_song_id eq $record->{song_id}) {
        $current_key = pause_key();
        clear_current_song();
    }
    clear_resume_selection() if $resume_song_id eq $record->{song_id};
    $displayed_tip_song_id = '' if $displayed_tip_song_id eq $record->{song_id};

    my $audit_note = audit_write({ action => 'SONG_ARCHIVED',
        id => $record->{song_id}, old => "Level $record->{level}",
        new => 'archived', detail => $record->{title} });
    return "Archived '$record->{title}' (ID $record->{song_id}). "
        . "History and attachments retained. Catalog backup: $backup.$audit_note";
}

sub restore_archived_song_category_entry {
    my ($records) = @_;
    my @archived = sort {
        $a->{level} <=> $b->{level}
            || lc($a->{title}) cmp lc($b->{title})
            || ($a->{line_no} // 0) <=> ($b->{line_no} // 0)
    } grep { $_->{archived} } @$records;
    return 'No archived songs to restore.' unless @archived;

    print "\nARCHIVED SONGS (practice history and media still retained)\n";
    print "--------------------------------------------------------\n";
    for my $i (0 .. $#archived) {
        printf "%3d. [%s] %s  (ID: %s)\n", $i + 1,
            $archived[$i]{level}, $archived[$i]{title}, $archived[$i]{song_id};
    }
    print "\nRestore which number? [Enter to cancel]: ";
    my $answer = <STDIN>;
    return 'Restore canceled.' unless defined $answer;
    $answer = trim_text($answer);
    return 'Restore canceled.' if $answer eq '';
    return "Invalid archive number '$answer'."
        unless $answer =~ /\A\d+\z/ && $answer >= 1 && $answer <= @archived;

    my $record = $archived[$answer - 1];
    print "Restore '$record->{title}' to " . level_label($record->{level})
        . " with the same song ID? [y/N]: ";
    my $confirm = <STDIN>;
    return 'Restore canceled.' unless defined($confirm) && lc(trim_text($confirm)) eq 'y';

    my ($backup, $backup_err) = backup_song_category_file();
    return $backup_err if defined $backup_err;

    my $old_number = $record->{number};
    $record->{archived} = 0;
    $record->{number} = count_songs_in_level($records, $record->{level});
    # The restored row is now one past the prior last visible number. Normalize
    # visible numbering without changing the IDs of other songs.
    normalize_song_numbers($records);
    my ($ok, $msg) = write_song_categories_tsv($records, $SONG_CATEGORY_FILE);
    if (!$ok) {
        $record->{archived} = 1;
        $record->{number} = $old_number;
        return "Restore failed; catalog backup: $backup. $msg";
    }
    my $audit_note = audit_write({ action => 'SONG_RESTORED',
        id => $record->{song_id}, old => 'archived',
        new => "Level $record->{level}", detail => $record->{title} });
    return "Restored '$record->{title}' (ID $record->{song_id}) to level "
        . "$record->{level}. History and attachments unchanged. Catalog backup: $backup.$audit_note";
}

sub add_song_category_entry {
    my ($records) = @_;

    print "New song title: ";
    chomp(my $title = <STDIN>);
    $title = trim_text($title);

    return 'Add canceled: blank title.' if $title eq '';
    return 'Add canceled: song titles may not contain tabs.' if $title =~ /\t/;

    print "Add to level, optionally with position, e.g. 2 or 2 3 or 2,3: ";
    chomp(my $where = <STDIN>);

    my ($level, $position, $err) = parse_level_and_optional_position($where);
    return $err if defined $err;

    return "Unknown level $level."
        unless valid_song_level($level);

    my $max_position = count_songs_in_level($records, $level) + 1;
    $position = $max_position if !defined $position;

    return "Position must be 1 through $max_position for level $level."
        if $position < 1 || $position > $max_position;

    my ($insert_ok, $insert_msg) = insert_song_record(
        $records, $level, $position, $title, max_song_line_no($records) + 1);
    return $insert_msg unless $insert_ok;

    my ($ok, $msg) = write_song_categories_tsv($records, $SONG_CATEGORY_FILE);
    return $msg unless $ok;
    my $added = find_song_record($records, $level, $position);
    my $audit_note = audit_write({ action => 'SONG_ADDED',
        id => $added->{song_id}, old => '', new => "Level $level position $position",
        detail => $title });
    return "Added '$title' to level $level at position $position. $msg$audit_note";
}

# Quick add from the main timer: level, title, done.
# Uses the same TSV read/insert/write logic as the song browser.
sub prompt_add_new_song_inner {
    ReadMode('restore');
    clear_screen();
    print "ADD NEW SONG\n";
    print "============\n\n";
    print "Choose a level:\n";
    for my $level (0 .. 6) {
        print "  $level = $by_key{$level}->{name}\n";
    }
    print "\nLevel (Enter to cancel): ";
    my $level_input = <STDIN>;
    if (!defined $level_input) {
        ReadMode('cbreak');
        $last_tick = time;
        return 'Add song canceled.';
    }
    my $level = trim_text($level_input);

    if ($level eq '') {
        ReadMode('cbreak');
        $last_tick = time;
        return 'Add song canceled.';
    }
    if ($level !~ /^[0-6]$/) {
        ReadMode('cbreak');
        $last_tick = time;
        return "Invalid level '$level'. Choose 0 through 6.";
    }

    print "Song title (Enter to cancel): ";
    my $title_input = <STDIN>;
    if (!defined $title_input) {
        ReadMode('cbreak');
        $last_tick = time;
        return 'Add song canceled.';
    }
    my $title = trim_text($title_input);
    if ($title eq '' || $title =~ /[\t\r\n]/) {
        ReadMode('cbreak');
        $last_tick = time;
        return 'Add song canceled: enter a nonblank title without tabs.';
    }

    my ($records, $warnings) = read_song_categories_tsv($SONG_CATEGORY_FILE);
    if (!defined $records) {
        ReadMode('cbreak');
        $last_tick = time;
        return join('; ', @$warnings);
    }

    # An archived song is invisible to the ordinary Find screen, but its title
    # still blocks duplicate Add. Offer to restore that exact permanent ID.
    my ($existing) = grep {
        song_title_identity($_->{title}) eq song_title_identity($title)
    } @$records;
    if ($existing) {
        if (!$existing->{archived}) {
            ReadMode('cbreak');
            $last_tick = time;
            return "NOT ADDED: '$existing->{title}' already exists in level "
                . "$existing->{level} (ID: $existing->{song_id}). "
                . "Use Find to practice it or Categories > Move to relocate it.";
        }
        print "\n'$existing->{title}' is already ARCHIVED (ID: $existing->{song_id}).\n";
        print "Restore it in level $level, preserving its song ID and history? [y/N]: ";
        my $confirm = <STDIN>;
        unless (defined($confirm) && lc(trim_text($confirm)) eq 'y') {
            ReadMode('cbreak');
            $last_tick = time;
            return "NOT ADDED: '$existing->{title}' is archived. Use Categories > Restore to bring it back.";
        }
        my ($backup, $backup_err) = backup_song_category_file();
        if (defined $backup_err) {
            ReadMode('cbreak');
            $last_tick = time;
            return "Restore failed: $backup_err";
        }
        my $old_level = $existing->{level};
        $existing->{archived} = 0;
        $existing->{level} = $level;
        $existing->{number} = count_songs_in_level($records, $level);
        my ($ok, $msg) = write_song_categories_tsv($records, $SONG_CATEGORY_FILE);
        ReadMode('cbreak');
        $last_tick = time;
        return "Restore failed; catalog backup: $backup. $msg" unless $ok;
        my ($check) = read_song_categories_tsv($SONG_CATEGORY_FILE);
        my ($found) = $check ? grep {
            ($_->{song_id} // '') eq $existing->{song_id} && !$_->{archived}
                && $_->{level} == $level
        } @$check : ();
        return "Restore saved but verification failed. Check $SONG_CATEGORY_FILE. Backup: $backup."
            unless $found;
        my $audit_note = audit_write({ action => 'SONG_RESTORED',
            id => $existing->{song_id}, old => "archived (level $old_level)",
            new => "Level $level", detail => $existing->{title} });
        return "RESTORED '$existing->{title}' in level $level (ID: $existing->{song_id}). "
            . "Original practice history preserved.$audit_note";
    }

    # Append at the end of the chosen level. Preserve existing IDs and generate
    # a unique, permanent ID for a new (not already active or archived) song.
    my $position = count_songs_in_level($records, $level) + 1;
    my ($insert_ok, $insert_msg) = insert_song_record(
        $records, $level, $position, $title, max_song_line_no($records) + 1);
    if (!$insert_ok) {
        ReadMode('cbreak');
        $last_tick = time;
        return $insert_msg;
    }
    my $added = find_song_record($records, $level, $position);
    my ($ok, $msg) = write_song_categories_tsv($records, $SONG_CATEGORY_FILE);

    ReadMode('cbreak');
    $last_tick = time;
    return "NOT ADDED: $msg" unless $ok;
    my ($check) = read_song_categories_tsv($SONG_CATEGORY_FILE);
    my ($found) = $check ? grep {
        ($_->{song_id} // '') eq $added->{song_id}
            && song_title_identity($_->{title}) eq song_title_identity($title)
            && !$_->{archived}
    } @$check : ();
    return "Add was written, but could not be verified in $SONG_CATEGORY_FILE. "
        . "Inspect that file before trying again." unless $found;
    my $audit_note = audit_write({ action => 'SONG_ADDED',
        id => $added->{song_id}, old => '', new => "Level $level position $position",
        detail => $title });
    return "ADDED [$level $position] $title (ID: $added->{song_id}).$audit_note";
}

# Don't let Add errors scroll away at the bottom of the main screen. This is
# especially useful when an archived song of the same title blocks an Add.
sub prompt_add_new_song {
    my $result = prompt_add_new_song_inner();
    ReadMode('restore');
    print "\n", $result, "\n\nPress Enter to return to the timer...";
    scalar <STDIN>;
    ReadMode('cbreak');
    $last_tick = time;
    return $result;
}

# Move supports the familiar [level number] reference and a title/ID search.
# Searching is administrative and never starts practice or changes the timer.
sub prompt_song_to_move {
    my ($records) = @_;
    print "\nMOVE SONG\n";
    print "---------\n";
    print "Enter [level number], e.g. 2 3, OR search by song title / permanent ID.\n";
    print "Song to move (Enter cancels): ";
    my $answer = <STDIN>;
    return (undef, 'Move canceled.') unless defined $answer;
    my $query = trim_text($answer);
    return (undef, 'Move canceled.') if $query eq '';

    if ($query =~ /^\d+\s*(?:,|\s+)\s*\d+\z/) {
        my ($level, $position, $err) = parse_song_ref($query);
        return (undef, $err) if defined $err;
        return (undef, "Unknown level $level.") unless valid_song_level($level);
        my $record = find_song_record($records, $level, $position);
        return (undef, "No active song at [$level $position].") unless $record;
        return ($record, undef);
    }

    my @matches = find_category_song_matches($records, $query);
    my @active = grep { !$_->{archived} } @matches;
    if (!@active) {
        return (undef, @matches
            ? "Only archived songs match '$query'. Restore one before moving it."
            : "No songs match '$query'. No changes made.");
    }

    my $text = "MOVE SONG: MATCHES FOR '$query'\n" . ('-' x 30) . "\n\n";
    for my $i (0 .. $#active) {
        my $song = $active[$i];
        $text .= sprintf("%3d. [%d %d] %s  (ID: %s)\n", $i + 1,
            $song->{level}, $song->{number}, $song->{title}, $song->{song_id});
    }
    $text .= "\nChoose the matching number below; this does not start practice.\n";
    print_paged_song_categories($text);
    print "Select song (1-" . scalar(@active) . "; Enter cancels): ";
    my $selection = <STDIN>;
    return (undef, 'Move canceled.') unless defined $selection;
    $selection = trim_text($selection);
    return (undef, 'Move canceled.') unless length($selection);
    return (undef, "Invalid selection '$selection'; no changes made.")
        unless $selection =~ /^\d+\z/ && $selection >= 1 && $selection <= @active;
    return ($active[$selection - 1], undef);
}

# Build the reordered catalog without touching the records currently shown in
# the menu. Removal closes the source gap; insertion shifts the destination's
# later rows. Both levels are then numbered 1,2,3,... and IDs are preserved.
sub preview_song_move {
    my ($records, $record, $dest_level, $dest_position) = @_;
    return (undef, 'Unknown destination level.') unless valid_song_level($dest_level);
    my @copy = map { +{ %$_ } } @$records;
    my $old_id = $record->{song_id};
    my $removed = remove_song_record(\@copy, $record);
    return (undef, 'Could not locate the source song; no changes made.') unless $removed;

    my $max_position = count_songs_in_level(\@copy, $dest_level) + 1;
    $dest_position = $max_position unless defined $dest_position;
    return (undef, "Position must be 1 through $max_position for level $dest_level.")
        if $dest_position < 1 || $dest_position > $max_position;

    my ($insert_ok, $insert_msg) = insert_song_record(
        \@copy, $dest_level, $dest_position, $record->{title},
        $record->{line_no}, $old_id);
    return (undef, $insert_msg) unless $insert_ok;

    my $found = find_song_record(\@copy, $dest_level, $dest_position);
    return (undef, 'Move could not be verified; no changes made.')
        unless $found && $found->{song_id} eq $old_id;
    # Move rebuilds the row rather than changing it in place; carry its
    # preceding comments into the new row as well.
    if ($record->{leading_comments}) {
        $found->{leading_comments} = [ @{ $record->{leading_comments} } ];
    }
    return (\@copy, undef);
}

sub move_song_category_entry {
    my ($records) = @_;
    my ($record, $err) = prompt_song_to_move($records);
    return $err if defined $err;

    my ($old_level, $old_position) = ($record->{level}, $record->{number});
    my $title = $record->{title};
    my $song_id = $record->{song_id};
    print "\nMove [$old_level $old_position] $title (ID: $song_id)\n";
    print "\nDESTINATION LEVELS\n";
    print "------------------\n";
    for my $level (0 .. 6) {
        printf "  %d = %-32s  (%d songs)\n", $level,
            $by_key{$level}{name}, count_songs_in_level($records, $level);
    }
    print "\nChoose destination level (0-6; optionally '3 4' for position 4; Enter cancels): ";
    my $input = <STDIN>;
    return 'Move canceled.' unless defined $input;
    my $where = trim_text($input);
    return 'Move canceled.' unless length($where);
    my ($dest_level, $dest_position, $dest_err) = parse_level_and_optional_position($where);
    return $dest_err if defined $dest_err;
    return "Unknown destination level $dest_level."
        unless valid_song_level($dest_level);

    my @there = sort { $a->{number} <=> $b->{number} }
        grep { !$_->{archived} && $_->{level} == $dest_level
            && ($_->{song_id} // '') ne $song_id } @$records;
    my $max_position = @there + 1;

    # A single level digit lets the user see the existing songs before choosing
    # exactly where the moved song will be placed; Enter means append.
    if (!defined $dest_position) {
        print "\n" . level_label($dest_level) . " (after removing source, if applicable)\n";
        print "----------------------------------------\n";
        if (@there) {
            for my $i (0 .. $#there) {
                printf "  %d. %s\n", $i + 1, $there[$i]{title};
            }
        }
        else {
            print "  (empty level)\n";
        }
        print "\nInsert at position 1-$max_position [Enter = append at $max_position]: ";
        my $position_input = <STDIN>;
        return 'Move canceled.' unless defined $position_input;
        $position_input = trim_text($position_input);
        if (length $position_input) {
            return "Invalid position '$position_input'. Enter a number from 1 to $max_position."
                unless $position_input =~ /^\d+\z/;
            $dest_position = 0 + $position_input;
        }
        else {
            $dest_position = $max_position;
        }
    }
    return "Position must be 1 through $max_position for level $dest_level; no changes made."
        if $dest_position < 1 || $dest_position > $max_position;

    return "'$title' is already at [$old_level $old_position]; no changes made."
        if $old_level == $dest_level && $old_position == $dest_position;

    my ($updated, $move_err) = preview_song_move($records, $record, $dest_level, $dest_position);
    return $move_err if defined $move_err;
    my ($backup, $backup_err) = backup_song_category_file();
    return $backup_err if defined $backup_err;

    my ($ok, $msg) = write_song_categories_tsv($updated, $SONG_CATEGORY_FILE);
    return "Move NOT saved. Original catalog backed up to $backup. $msg" unless $ok;
    @$records = @$updated;

    my $audit_note = audit_write({ action => 'SONG_MOVED', id => $song_id,
        old => "Level $old_level position $old_position",
        new => "Level $dest_level position $dest_position", detail => $title });
    return "Moved '$title' [$old_level $old_position] -> [$dest_level $dest_position]. "
        . "Both levels renumbered without gaps; permanent ID $song_id retained. "
        . "Catalog backup: $backup.$audit_note";
}

# Optional, backward-compatible MP3 storage. Multiple rows with the same
# permanent song ID are tracks in playlist order. Legacy one-row data loads
# unchanged. As with tabs, ignore duplicate paths without deleting any files.
# Rename through this menu to create an audit event. Direct manual edits to
# a TSV cannot be attributed to a user action and are not backfilled.
sub rename_song_category_entry {
    my ($records) = @_;
    my ($record, $err) = prompt_song_reference(
        "Song to rename (level and number, e.g. 2 3): ", $records,
    );
    return $err if defined $err;
    print "Current title: $record->{title}\nNew title (Enter cancels): ";
    my $input = <STDIN>;
    return 'Rename canceled.' unless defined $input;
    my $new = trim_text($input);
    return 'Rename canceled.' unless length($new);
    return 'Rename canceled: tabs or line breaks are not allowed.'
        if $new =~ /[\t\r\n]/;
    my $old = $record->{title};
    return 'Title unchanged.' if $old eq $new;
    for my $other (@$records) {
        next if $other->{song_id} eq $record->{song_id};
        return "That title is already used by '$other->{title}'."
            if song_title_identity($other->{title}) eq song_title_identity($new);
    }
    print "Rename '$old' to '$new' (keeping ID $record->{song_id})? [y/N]: ";
    my $answer = <STDIN>;
    return 'Rename canceled.' unless defined($answer)
        && lc(trim_text($answer)) eq 'y';
    $record->{title} = $new;
    my ($ok, $msg) = write_song_categories_tsv($records, $SONG_CATEGORY_FILE);
    if (!$ok) { $record->{title} = $old; return $msg; }
    $current_song_title = $new if $current_song_id eq $record->{song_id};
    $resume_song_title = $new if $resume_song_id eq $record->{song_id};
    my $audit_note = audit_write({ action => 'SONG_RENAMED',
        id => $record->{song_id}, old => $old, new => $new,
        detail => "Level $record->{level}" });
    return "Renamed '$old' to '$new' (ID unchanged).$audit_note";
}

sub read_song_audio {
    my %audio;
    return \%audio unless -e $SONG_AUDIO_FILE;
    open my $fh, '<', $SONG_AUDIO_FILE or return \%audio;
    while (my $line = <$fh>) {
        chomp $line;
        $line =~ s/\r\z//;
        next if $line =~ /^\s*\z/;
        my ($id, $path) = split /\t/, $line, 2;
        next unless defined($id) && length($id) && defined($path) && length($path);
        next if grep { lc($_) eq lc($path) } @{ $audio{$id} // [] };
        push @{ $audio{$id} }, $path;
    }
    close $fh;
    return \%audio;
}

sub save_song_audio {
    my ($audio) = @_;
    my $before = read_song_audio();
    open my $fh, '>', $SONG_AUDIO_FILE
        or return (0, "Cannot write $SONG_AUDIO_FILE: $!");
    for my $id (sort keys %$audio) {
        for my $path (@{ $audio->{$id} // [] }) {
            next unless defined($path) && length($path);
            print $fh "$id\t$path\n";
        }
    }
    close $fh or return (0, "Cannot close $SONG_AUDIO_FILE: $!");
    my $note = audit_media_changes($before, $audio, 'mp3');
    return (1, 'MP3 associations saved.' . $note);
}

sub vlc_program {
    if ($^O eq 'MSWin32') {
        for my $root ($ENV{ProgramFiles}, $ENV{'ProgramFiles(x86)'}, $ENV{LOCALAPPDATA}) {
            next unless defined($root) && length($root);
            my $path = "$root\\VideoLAN\\VLC\\vlc.exe";
            return $path if -f $path;
        }
        # For installations added to PATH.
        return 'vlc.exe';
    }
    return 'vlc';
}

# A single M3U input makes VLC load ALL MP3s together as one playlist,
# including when it is already running in single-instance mode. Launching
# each MP3 separately with --no-playlist-enqueue would instead replace the
# preceding track. Keep the generated playlist file available for VLC to read.
# The name is unique to this Perl process; repeated selections overwrite it.
sub write_vlc_playlist {
    my ($files) = @_;
    return (undef, 'No MP3s to add to the VLC playlist.') unless @$files;
    my $playlist = File::Spec->catfile(
        File::Spec->tmpdir(), "practice_timer_vlc_$$.m3u8"
    );
    open my $fh, '>:raw', $playlist
        or return (undef, "Could not create VLC playlist $playlist: $!");
    print {$fh} "#EXTM3U\n";
    for my $file (@$files) {
        my $absolute = File::Spec->rel2abs($file);
        print {$fh} "$absolute\n";
    }
    close $fh or return (undef, "Could not finish VLC playlist $playlist: $!");
    return ($playlist, undef);
}

sub open_song_in_vlc {
    my ($id) = @_;
    my $audio = read_song_audio();
    my @files = @{ $audio->{$id} // [] };
    return '' unless @files;

    # Missing files must not prevent other attached MP3s from playing.
    my @existing = grep { -f $_ } @files;
    my @missing  = grep { !-f $_ } @files;
    return 'MP3 files missing: ' . join('; ', @missing) unless @existing;

    my $vlc = vlc_program();
    my $input = $existing[0];
    if (@existing > 1) {
        my ($playlist, $err) = write_vlc_playlist(\@existing);
        return $err if defined $err;
        $input = $playlist;
    }

    # One VLC launch, one playlist. Replace its previous playlist and start
    # immediately, whether this is a fresh VLC or a reused window.
    my @args = ($vlc, '--one-instance', '--no-playlist-enqueue', $input);
    my $status = @existing == 1 ? 'MP3 started in VLC' :
        scalar(@existing) . ' MP3s loaded into VLC playlist; first track playing';
    $status .= '; ' . scalar(@missing) . ' missing MP3(s) skipped' if @missing;

    if ($^O eq 'MSWin32') {
        # Windows Perl system(1, LIST) starts VLC without blocking.
        my $pid = system(1, @args);
        return $pid == -1 ? "Could not launch VLC ($vlc): $!" : "$status (reuse existing window when configured).";
    }

    my $pid = fork();
    return "Could not launch VLC: $!" unless defined $pid;
    if ($pid == 0) {
        exec { $vlc } @args or POSIX::_exit(127);
    }
    return "$status (reuse existing window when configured).";
}

# Song materials: one TSV row per TXT, PDF, ODT, JPG, or PNG; unlimited files per song.
# Older single-file practice_song_tabs.tsv files load without conversion.
sub read_song_tabs {
    my %tabs;
    return \%tabs unless -e $SONG_TAB_FILE;
    open my $fh, '<', $SONG_TAB_FILE or return \%tabs;
    while (my $line = <$fh>) {
        chomp $line;
        $line =~ s/\r\z//;
        next if $line =~ /^\s*\z/;
        my ($id, $path) = split /\t/, $line, 2;
        next unless defined($id) && length($id) && defined($path) && length($path);
        # File order is retained. Skip exact duplicates from hand-edited TSVs.
        my $present = grep { lc($_) eq lc($path) } @{ $tabs{$id} // [] };
        push @{ $tabs{$id} }, $path unless $present;
    }
    close $fh;
    return \%tabs;
}

sub save_song_tabs {
    my ($tabs) = @_;
    my $before = read_song_tabs();
    open my $fh, '>', $SONG_TAB_FILE
        or return (0, "Cannot write $SONG_TAB_FILE: $!");
    for my $id (sort keys %$tabs) {
        for my $path (@{ $tabs->{$id} // [] }) {
            next unless defined($path) && length($path);
            print $fh "$id\t$path\n";
        }
    }
    close $fh or return (0, "Cannot close $SONG_TAB_FILE: $!");
    my $note = audit_media_changes($before, $tabs, 'tab_or_document');
    return (1, 'Song materials saved.' . $note);
}

sub gvim_program {
    return 'gvim' unless $^O eq 'MSWin32';
    my @roots = grep { defined($_) && length($_) }
        ($ENV{ProgramFiles}, $ENV{'ProgramFiles(x86)'}, $ENV{LOCALAPPDATA},
         $ENV{'ProgramW6432'}, 'C:\\');
    for my $root (@roots) {
        for my $base ("$root\\Vim", "$root\\Programs\\Vim") {
            next unless -d $base;
            for my $version (qw(vim93 vim92 vim91 vim90 vim82 vim81 vim80)) {
                my $file = "$base\\$version\\gvim.exe";
                return $file if -f $file;
            }
            my $direct = "$base\\gvim.exe";
            return $direct if -f $direct;
        }
    }
    return 'gvim.exe';
}

# Attached .txt files use Notepad on Windows, independent of default
# file associations. The historical activity report still uses gVim.
sub notepad_program {
    return 'notepad.exe' if $^O eq 'MSWin32';
    return 'notepad'; # Non-Windows fallback; Windows is the supported platform.
}

sub firefox_program {
    return 'firefox' unless $^O eq 'MSWin32';
    for my $root ($ENV{ProgramFiles}, $ENV{'ProgramFiles(x86)'}, $ENV{LOCALAPPDATA}) {
        next unless defined($root) && length($root);
        for my $path ("$root\\Mozilla Firefox\\firefox.exe", "$root\\Programs\\Mozilla Firefox\\firefox.exe") {
            return $path if -f $path;
        }
    }
    return 'firefox.exe';  # Fallback when Firefox is on PATH.
}

# Locate OpenOffice Writer without relying on Windows file associations.
# A missing executable is reported explicitly so an ODT is never silently
# launched in a different program. The user may override detection above.
sub openoffice_writer_program {
    if (length $OPENOFFICE_WRITER_EXE) {
        return (-f $OPENOFFICE_WRITER_EXE)
            ? ($OPENOFFICE_WRITER_EXE, [])
            : (undef, "OpenOffice Writer path not found: $OPENOFFICE_WRITER_EXE. "
                . 'Fix $OPENOFFICE_WRITER_EXE near the top of practice_timer.pl.');
    }

    if ($^O eq 'MSWin32') {
        my %seen;
        my @roots = grep { defined($_) && length($_) && !$seen{lc($_)}++ }
            ($ENV{ProgramFiles}, $ENV{'ProgramFiles(x86)'},
             $ENV{ProgramW6432}, $ENV{LOCALAPPDATA});
        my @install_dirs = ('OpenOffice 4', 'OpenOffice 5',
            'OpenOffice.org 3', 'Apache OpenOffice 4', 'OpenOffice');
        for my $root (@roots) {
            for my $dir (@install_dirs) {
                my $program_dir = "$root\\$dir\\program";
                my $writer = "$program_dir\\swriter.exe";
                return ($writer, []) if -f $writer;
                my $office = "$program_dir\\soffice.exe";
                return ($office, ['-writer']) if -f $office;
            }
        }

        # Also support portable installations or a custom PATH entry.
        for my $dir (split /;/, ($ENV{PATH} // '')) {
            $dir =~ s/^\s*"|"\s*$//g;
            next unless length $dir;
            for my $entry (['swriter.exe', []], ['soffice.exe', ['-writer']]) {
                my $program = "$dir\\$entry->[0]";
                return ($program, $entry->[1]) if -f $program;
            }
        }
        return (undef, 'OpenOffice Writer not found. Expected swriter.exe in '
            . 'the OpenOffice installation (for example, '
            . 'C:\\Program Files (x86)\\OpenOffice 4\\program\\swriter.exe). '
            . 'Set $OPENOFFICE_WRITER_EXE near the top of practice_timer.pl '
            . 'to the actual path.');
    }

    # Non-Windows: find the native launcher on PATH.
    for my $dir (split /:/, ($ENV{PATH} // '')) {
        next unless length $dir;
        for my $entry (['swriter', []], ['soffice', ['-writer']]) {
            my $program = "$dir/$entry->[0]";
            return ($program, $entry->[1]) if -x $program;
        }
    }
    return (undef, 'OpenOffice Writer not found on PATH. '
        . 'Set $OPENOFFICE_WRITER_EXE to the Writer executable path.');
}

# JPG/JPEG/PNG attachments always open with IrfanView, regardless of Windows
# image file associations.  Prefer 64-bit, but also support 32-bit and portable
# installations.  Never silently fall back to Paint or another viewer.
sub irfanview_program {
    return (undef, 'IrfanView is configured here for Windows only.')
        unless $^O eq 'MSWin32';

    if (length $IRFANVIEW_EXE) {
        return (-f $IRFANVIEW_EXE)
            ? ($IRFANVIEW_EXE, undef)
            : (undef, "IrfanView path not found: $IRFANVIEW_EXE. "
                . 'Fix $IRFANVIEW_EXE near the top of practice_timer.pl.');
    }

    my %seen;
    my @roots = grep { defined($_) && length($_) && !$seen{lc($_)}++ }
        ($ENV{ProgramFiles}, $ENV{'ProgramFiles(x86)'},
         $ENV{ProgramW6432}, $ENV{LOCALAPPDATA});
    for my $root (@roots) {
        for my $folder ('IrfanView', 'Programs\IrfanView') {
            for my $exe ('i_view64.exe', 'i_view32.exe') {
                my $path = "$root\\$folder\\$exe";
                return ($path, undef) if -f $path;
            }
        }
    }

    # Portable IrfanView can be made available on PATH.
    for my $dir (split /;/, ($ENV{PATH} // '')) {
        $dir =~ s/^\s*"|"\s*$//g;
        next unless length $dir;
        for my $exe ('i_view64.exe', 'i_view32.exe') {
            my $path = "$dir\\$exe";
            return ($path, undef) if -f $path;
        }
    }

    return (undef, 'IrfanView not found in the usual Windows install folders '
        . 'or PATH. Set $IRFANVIEW_EXE near the top of practice_timer.pl '
        . 'to the full path to i_view64.exe or i_view32.exe.');
}

# Return the Audacity executable, or a useful message telling the user how
# to configure it. Do not rely on the Windows default MP3 player association.
sub audacity_program {
    if (length $AUDACITY_EXE) {
        return -f $AUDACITY_EXE
            ? ($AUDACITY_EXE, undef)
            : (undef, "Audacity path not found: $AUDACITY_EXE. "
                . 'Set $AUDACITY_EXE near the top of practice_timer.pl.');
    }

    if ($^O eq 'MSWin32') {
        my %seen;
        my @roots = grep { defined($_) && length($_) && !$seen{lc($_)}++ }
            ($ENV{ProgramFiles}, $ENV{'ProgramFiles(x86)'},
             $ENV{ProgramW6432}, $ENV{LOCALAPPDATA});
        for my $root (@roots) {
            for my $dir ('Audacity', 'Audacity 4', 'Audacity 3',
                         'Programs\\Audacity') {
                my $candidate = "$root\\$dir\\Audacity.exe";
                return ($candidate, undef) if -f $candidate;
            }
            # Accommodate versioned installation directories, e.g. Audacity 3.7.
            if (opendir my $dh, $root) {
                my @names = sort grep { /^Audacity(?:\s|$)/i } readdir $dh;
                closedir $dh;
                for my $name (@names) {
                    my $candidate = "$root\\$name\\Audacity.exe";
                    return ($candidate, undef) if -f $candidate;
                }
            }
        }
        for my $dir (split /;/, ($ENV{PATH} // '')) {
            $dir =~ s/^\s*"|"\s*$//g;
            next unless length $dir;
            my $candidate = "$dir\\audacity.exe";
            return ($candidate, undef) if -f $candidate;
        }
        return (undef, 'Audacity.exe was not found in the usual Windows '
            . 'installation folders or PATH. Set $AUDACITY_EXE near the top '
            . 'of practice_timer.pl to the full path to Audacity.exe.');
    }

    for my $dir (split /:/, ($ENV{PATH} // '')) {
        next unless length $dir;
        my $candidate = "$dir/audacity";
        return ($candidate, undef) if -x $candidate;
    }
    return (undef, 'Audacity not found on PATH. Set $AUDACITY_EXE '
        . 'near the top of practice_timer.pl.');
}

# Nonblocking launch: timer keeps running while editors/browser remain open.
sub launch_song_material_program {
    my (@args) = @_;
    my $program = $args[0];
    if ($^O eq 'MSWin32') {
        my $pid = system(1, @args);
        return $pid == -1 ? "Could not launch $program: $!" : '';
    }
    my $pid = fork();
    return "Could not launch $program: $!" unless defined $pid;
    if ($pid == 0) {
        exec { $program } @args or POSIX::_exit(127);
    }
    return '';
}

# Firefox's -new-tab expects a URL. Encode local paths, including spaces,
# into file: URLs; Windows drive letters and UNC paths are both accepted.
sub firefox_file_url {
    my ($path) = @_;
    $path =~ s{\\}{/}g;
    my $prefix = 'file://';
    if ($path =~ m{^//}) {
        $path =~ s{^//}{}; # UNC: file://server/share/file.pdf
    }
    elsif ($path =~ m{^[A-Za-z]:/}) {
        $prefix = 'file:///';
    }
    elsif ($path =~ m{^/}) {
        $prefix = 'file://';
    }
    else {
        $prefix = 'file:///';
    }
    # Operate on UTF-8 bytes for reliable percent encoding.
    require Encode;
    my $bytes = Encode::encode('UTF-8', $path);
    $bytes =~ s{([^A-Za-z0-9/._~:\-])}{sprintf('%%%02X', ord($1))}ge;
    return $prefix . $bytes;
}

sub open_one_song_material {
    my ($file) = @_;
    return "Material missing: $file" unless -f $file;
    if ($file =~ /\.pdf\z/i) {
        my $firefox = firefox_program();
        my $err = launch_song_material_program($firefox, '-new-tab', firefox_file_url($file));
        return length($err) ? $err : 'Opened PDF in Firefox.';
    }
    if ($file =~ /\.txt\z/i) {
        my $err = launch_song_material_program(notepad_program(), $file);
        return length($err) ? $err : 'Opened TXT in Notepad.';
    }
    if ($file =~ /\.odt\z/i) {
        my ($writer, $issue) = openoffice_writer_program();
        return $issue unless defined $writer;
        my $err = launch_song_material_program($writer, @$issue, $file);
        return length($err) ? $err : 'Opened ODT in OpenOffice Writer.';
    }
    if ($file =~ /\.(?:jpe?g|png)\z/i) {
        my ($irfanview, $issue) = irfanview_program();
        return $issue unless defined $irfanview;
        my $err = launch_song_material_program($irfanview, $file);
        return length($err) ? $err : 'Opened image in IrfanView.';
    }
    return "Unsupported material type: $file";
}

# Open TXT in Notepad, PDF in Firefox, ODT in Writer, and JPG/PNG in IrfanView.
sub open_song_materials {
    my ($id) = @_;
    my $tabs = read_song_tabs();
    my @files = @{ $tabs->{$id} // [] };
    return '' unless @files;
    my (@txt, @pdf, @odt, @images, @missing);
    for my $file (@files) {
        if (!-f $file) { push @missing, $file; next; }
        if ($file =~ /\.txt\z/i) { push @txt, $file; }
        elsif ($file =~ /\.pdf\z/i) { push @pdf, $file; }
        elsif ($file =~ /\.odt\z/i) { push @odt, $file; }
        elsif ($file =~ /\.(?:jpe?g|png)\z/i) { push @images, $file; }
    }
    my @messages;
    if (@txt) {
        # One file per launch avoids different Notepad versions silently
        # ignoring additional filenames on their command line.
        my $opened = 0;
        for my $file (@txt) {
            my $err = launch_song_material_program(notepad_program(), $file);
            if (length $err) { push @messages, $err; }
            else { $opened++; }
        }
        push @messages, "$opened TXT in Notepad." if $opened;
    }
    for my $file (@pdf) {
        my $firefox = firefox_program();
        my $err = launch_song_material_program($firefox, '-new-tab', firefox_file_url($file));
        push @messages, $err if length($err);
    }
    push @messages, scalar(@pdf) . ' PDF in Firefox.' if @pdf;
    if (@odt) {
        my ($writer, $issue) = openoffice_writer_program();
        if (!defined $writer) {
            push @messages, $issue;
        }
        else {
            my $err = launch_song_material_program($writer, @$issue, @odt);
            push @messages, length($err) ? $err
                : scalar(@odt) . ' ODT in OpenOffice Writer.';
        }
    }
    if (@images) {
        my ($irfanview, $issue) = irfanview_program();
        if (!defined $irfanview) {
            push @messages, $issue;
        }
        else {
            # Start each attached image separately so all images open reliably.
            my $opened = 0;
            for my $file (@images) {
                my $err = launch_song_material_program($irfanview, $file);
                if (length $err) { push @messages, $err; }
                else { $opened++; }
            }
            push @messages, "$opened image(s) in IrfanView." if $opened;
        }
    }
    push @messages, scalar(@missing) . ' missing material file(s).' if @missing;
    return join(' ', @messages);
}

# One attachment hotkey for songs, Scales, Ear training, and Theory. TSVs stay:
# any number of MP3 rows in practice_song_audio.tsv, and any number of
# TXT/PDF/ODT/JPG/JPEG/PNG rows in practice_song_tabs.tsv.
sub media_attachment_kind {
    my ($filename) = @_;
    return 'mp3' if defined($filename) && $filename =~ /\.mp3\z/i;
    return 'tab' if defined($filename) && $filename =~ /\.(?:txt|pdf|odt|jpe?g|png)\z/i;
    return '';
}

# Choose the default folder based only on the extension, not on the command
# used to reach the menu. Absolute local paths are used unchanged.
sub resolve_media_attachment_path {
    my ($entered) = @_;
    my $kind = media_attachment_kind($entered);
    return (undef, undef) unless length $kind;

    my $file = $entered;
    if ($file !~ m{^(?:[A-Za-z]:[\\/]|[\\/])}) {
        my $folder = $kind eq 'mp3' ? $SONG_AUDIO_DIR : $SONG_TAB_DIR;
        $file = $folder . '\\' . $file;
    }
    return ($kind, $file);
}

# Sort media displays by filename (not drive/folder), ignoring case.
# Preserve the original attachment-list index so -N can remove the exact
# displayed item without changing the order stored in the media TSVs.
sub media_sort_filename {
    my ($path) = @_;
    $path //= '';
    $path =~ s{^.*[\\/]}{};
    return lc $path;
}

sub media_entries_for_owner {
    my ($id, $audio, $tabs) = @_;
    my @items;
    my $index = 0;
    for my $path (@{ $audio->{$id} // [] }) {
        push @items, { kind => 'mp3', path => $path, source_index => $index++ };
    }
    $index = 0;
    for my $path (@{ $tabs->{$id} // [] }) {
        push @items, { kind => 'tab', path => $path, source_index => $index++ };
    }
    return sort {
        media_sort_filename($a->{path}) cmp media_sort_filename($b->{path})
            || lc($a->{path}) cmp lc($b->{path})
            || $a->{path} cmp $b->{path}
            || $a->{kind} cmp $b->{kind}
            || $a->{source_index} <=> $b->{source_index}
    } @items;
}

# Compare only the meaningful letters and numbers. In particular, ignore
# capitalization, underscores/spaces, apostrophes, quotes and punctuation.
# A compact beginning match also permits filenames with suffixes such as
# "_live", " (alternate)", or "2". Such candidates ALWAYS need approval.
sub normalized_media_stem {
    my ($name) = @_;
    $name //= '';
    $name = lc $name;
    $name =~ s/[^[:alnum:]]+//g;
    return $name;
}

# Some real song catalog titles and IDs have extra legacy handles appended,
# e.g. title "Boulevard of Broken Dreams boulevard_dreams" and ID
# "boulevard_of_broken_dreams_boulevard_dreams".  In that situation the
# ordinary MP3 filename "Boulevard of Broken Dreams.mp3" is a *complete*
# prefix of the catalog label, not an exact match.  Test at a word boundary
# and require a meaningful multiword filename to avoid broad partial matches.
sub media_stem_is_catalog_prefix {
    my ($stem, $owner) = @_;
    my $file_slug = lc($stem // '');
    $file_slug =~ s/[^[:alnum:]]+/_/g;
    $file_slug =~ s/^_+|_+$//g;
    my $owner_slug = lc($owner // '');
    $owner_slug =~ s/[^[:alnum:]]+/_/g;
    $owner_slug =~ s/^_+|_+$//g;
    return 0 unless $file_slug =~ /_/ && length(normalized_media_stem($stem)) >= 8;
    return index($owner_slug, $file_slug . '_') == 0 ? 1 : 0;
}

# Look only in the two configured default folders (not recursively).
# Check both the human-readable song title and its permanent ID. Some IDs
# include an additional handle (e.g., boulevard_of_broken_dreams_boulevard_dreams)
# which does not appear in a perfectly matching filename. Suggestions still
# require explicit approval. Display them alphabetically by filename.
# Optional directory arguments make this independently testable.
sub scan_media_candidates {
    my ($id, $title, $audio, $tabs, $audio_dir, $tab_dir) = @_;
    $audio_dir //= $SONG_AUDIO_DIR;
    $tab_dir   //= $SONG_TAB_DIR;
    my $id_needle = normalized_media_stem($id);
    my $title_needle = normalized_media_stem($title);
    return ([], ['No usable song title or ID for filename matching.'])
        unless length($id_needle) || length($title_needle);

    my %attached = map { lc($_) => 1 }
        grep { defined($_) && length($_) }
        (@{ $audio->{$id} // [] }, @{ $tabs->{$id} // [] });
    my (@matches, @issues);
    for my $pair ([$audio_dir, 'mp3'], [$tab_dir, 'tab']) {
        my ($dir, $wanted_kind) = @$pair;
        my $dh;
        if (!opendir($dh, $dir)) {
            push @issues, "Could not scan $dir: $!";
            next;
        }
        my @names = readdir($dh);
        closedir($dh);
        for my $name (@names) {
            next if $name eq '.' || $name eq '..';
            next if $name =~ /[\t\r\n]/; # TSV storage requires one path per line.
            my $kind = media_attachment_kind($name);
            next unless $kind eq $wanted_kind;
            my $path = File::Spec->catfile($dir, $name);
            next unless -f $path;
            next if $attached{lc($path)};
            (my $stem = $name) =~ s/\.[^.]+\z//;
            my $normalized = normalized_media_stem($stem);
            next unless length $normalized;
            my $match_rank;
            if (length($title_needle) && $normalized eq $title_needle) {
                $match_rank = 0; # exact displayed title
            }
            elsif (length($id_needle) && $normalized eq $id_needle) {
                $match_rank = 1; # exact permanent ID
            }
            elsif (length($title_needle) && index($normalized, $title_needle) == 0) {
                $match_rank = 2; # title followed by a suffix, e.g. (live)
            }
            elsif (length($id_needle) && index($normalized, $id_needle) == 0) {
                $match_rank = 3; # ID followed by a suffix
            }
            elsif (media_stem_is_catalog_prefix($stem, $title)
                   || media_stem_is_catalog_prefix($stem, $id)) {
                $match_rank = 4; # exact filename followed by legacy handle in catalog
            }
            else {
                next;
            }
            push @matches, {
                kind => $kind, path => $path, filename => $name,
                directory => $wanted_kind, match_rank => $match_rank,
            };
        }
    }
    @matches = sort {
        lc($a->{filename}) cmp lc($b->{filename})
            || $a->{filename} cmp $b->{filename}
            || $a->{directory} cmp $b->{directory}
            || lc($a->{path}) cmp lc($b->{path})
    } @matches;
    return (\@matches, \@issues);
}

# A numbered choice IS approval. All selected MP3s may be attached,
# along with any number of other file types. Validate before changing data.
sub parse_media_candidate_selection {
    my ($input, $candidates) = @_;
    return (undef, 'No suggested files to choose from.') unless @$candidates;
    my @indices;
    if (lc($input) eq 'all') {
        @indices = (0 .. $#$candidates);
    }
    elsif ($input =~ /^\d+(?:\s*,\s*\d+)*\z/) {
        @indices = map { $_ - 1 } split /\s*,\s*/, $input;
    }
    else {
        return (undef, 'Use candidate numbers separated by commas, or all.');
    }
    my %seen;
    my @chosen;
    for my $index (@indices) {
        return (undef, 'Candidate number is out of range.')
            if $index < 0 || $index > $#$candidates;
        next if $seen{$index}++;
        push @chosen, $candidates->[$index];
    }
    return (\@chosen, undef);
}

# Candidate approval modifies TSV associations only, without launching VLC.
# MP3 order is the order selected in the approval dialog. A later song
# selection launches the entire saved playlist and starts the first track.
sub add_approved_media_candidates {
    my ($id, $title, $chosen, $audio, $tabs) = @_;
    my $audio_changed = 0;
    my $tab_changed = 0;
    my $count = 0;
    for my $candidate (@$chosen) {
        my $path = $candidate->{path};
        next unless -f $path;
        if ($candidate->{kind} eq 'mp3') {
            my $list = $audio->{$id} // [];
            next if grep { lc($_) eq lc($path) } @$list;
            push @$list, $path;
            $audio->{$id} = $list;
            $audio_changed = 1;
            $count++;
        }
        else {
            my $list = $tabs->{$id} // [];
            next if grep { lc($_) eq lc($path) } @$list;
            push @$list, $path;
            $tabs->{$id} = $list;
            $tab_changed = 1;
            $count++;
        }
    }
    my @errors;
    if ($audio_changed) {
        my ($ok, $message) = save_song_audio($audio);
        push @errors, $message unless $ok;
    }
    if ($tab_changed) {
        my ($ok, $message) = save_song_tabs($tabs);
        push @errors, $message unless $ok;
    }
    return join(' ', @errors) if @errors;
    return $count
        ? "Attached $count suggested file(s) to $title. MP3s play together as one VLC playlist."
        : 'No new files attached (already attached or no longer found).';
}

# Open ONE already-attached media item without changing the selected song,
# its category, or its practice-selection count. Open MP3s individually here;
# the original open_song_in_vlc() still assembles the full playlist for "o".
sub open_one_attached_media {
    my ($item) = @_;
    return 'No attachment selected.' unless defined $item;
    my $path = $item->{path} // '';
    return 'Attachment path is empty.' unless length $path;
    if (($item->{kind} // '') eq 'mp3') {
        return "MP3 file not found: $path" unless -f $path;
        my $err = launch_song_material_program(
            vlc_program(), '--one-instance', '--no-playlist-enqueue', $path);
        return length($err) ? $err : "Opened MP3 in VLC: $path";
    }
    return open_one_song_material($path);
}

# Parse a list of numbered OPEN commands for attached media. Accept
# "o2 o4 o5" (or "o2,o4,o5") in addition to the existing single "o2".
# All numbers refer to the ATTACHED list, not the suggested-file list.
# Validate the entire request before launching anything, and avoid opening
# the same item twice if a number was repeated.
sub parse_attached_media_open_selection {
    my ($input, $items) = @_;
    $input //= '';
    $input = trim_text($input);
    return (undef, 'Use oN commands separated by spaces or commas (for example: o2 o4 o5).')
        unless $input =~ /\Ao[1-9]\d*(?:(?:\s*,\s*|\s+)o[1-9]\d*)*\z/i;
    my (@indices, %seen);
    for my $token (split /[\s,]+/, $input) {
        my ($number) = $token =~ /\Ao([1-9]\d*)\z/i;
        # Guard against an absurdly long number before numeric conversion.
        return (undef, "Invalid attachment number: $token") if length($number) > 8;
        my $index = $number - 1;
        return (undef, "No attached media has number $number. Nothing opened.")
            if $index > $#$items;
        push @indices, $index unless $seen{$index}++;
    }
    return (\@indices, undef);
}

# Open only selected attachments; if two or more MP3s are selected, start
# one VLC playlist rather than replacing the preceding track with each launch.
# Other media types open individually in their configured applications.
# No session, category, selection-count, or attachment TSV state is changed.
sub open_selected_attached_media {
    my ($selected) = @_;
    return 'No attached media selected.' unless @$selected;
    return open_one_attached_media($selected->[0]) if @$selected == 1;

    my @mp3s = map { $_->{path} }
        grep { ($_->{kind} // '') eq 'mp3' } @$selected;
    my @messages;
    if (@mp3s) {
        my @existing = grep { -f $_ } @mp3s;
        my @missing  = grep { !-f $_ } @mp3s;
        if (@existing) {
            my $input = $existing[0];
            my $playlist_problem;
            if (@existing > 1) {
                ($input, $playlist_problem) = write_vlc_playlist(\@existing);
            }
            if (defined $playlist_problem) {
                push @messages, $playlist_problem;
            }
            else {
                my $err = launch_song_material_program(
                    vlc_program(), '--one-instance', '--no-playlist-enqueue', $input);
                push @messages, length($err) ? $err : (@existing > 1
                    ? scalar(@existing) . ' selected MP3s opened as one VLC playlist.'
                    : 'Selected MP3 opened in VLC.');
            }
        }
        push @messages, scalar(@missing) . ' selected MP3 file(s) missing.' if @missing;
    }
    for my $item (@$selected) {
        next if ($item->{kind} // '') eq 'mp3';
        my $message = open_one_song_material($item->{path});
        push @messages, $message if length $message;
    }
    return @messages ? join(' ', @messages) : 'No selected media was opened.';
}

# Open ALL currently attached media as with the All selection prompt,
# including the full playlist if there are multiple MP3s.
sub open_all_attached_media {
    my ($id) = @_;
    my $audio = read_song_audio();
    my $tabs  = read_song_tabs();
    return 'No media is attached.'
        unless @{ $audio->{$id} // [] } || @{ $tabs->{$id} // [] };
    my @messages = grep { length($_) }
        (open_song_in_vlc($id), open_song_materials($id));
    return @messages ? join(' ', @messages) : 'No associated media was opened.';
}

# All local media for songs, Scales, Ear training, and Theory use t(k):
# MP3 -> VLC and G:\My Drive\mp3; everything else -> G:\My Drive\tab.
# oN opens attached item N; o2 o4 o5 opens several; o opens everything.
# -N removes a displayed attachment; - clears everything for this owner.
sub prompt_current_song_media {
    my ($material_id, $material_title) = current_material_owner();
    if (!defined $material_id) {
        $last_message = 'Select a song (P/f), Scales (s), Ear training (h), or Theory (y); then press t for media.';
        return;
    }

    ReadMode('restore');
    clear_screen();
    my $audio = read_song_audio();
    my $tabs  = read_song_tabs();
    my @items = media_entries_for_owner($material_id, $audio, $tabs);

    print "Media for $material_title\n";
    print "----------------------------\n";
    if (@items) {
        for my $i (0 .. $#items) {
            my $label = $items[$i]->{kind} eq 'mp3' ? 'MP3' :
                ($items[$i]->{path} =~ /\.([^.\\\/]+)\z/ ? uc($1) : 'FILE');
            printf "%2d. %-4s %s\n", $i + 1, $label, $items[$i]->{path};
        }
    }
    else {
        print "(none attached)\n";
    }
    my ($candidates, $scan_issues) = scan_media_candidates(
        $material_id, $material_title, $audio, $tabs);
    print "\nSUGGESTED FILES (matched against song title or ID)\n";
    if (@$candidates) {
        for my $i (0 .. $#$candidates) {
            my $c = $candidates->[$i];
            my @match_labels = ('exact title', 'exact ID', 'starts with title', 'starts with ID', 'catalog title/ID has extra suffix');
            my $label = $match_labels[$c->{match_rank}];
            my ($extension) = $c->{filename} =~ /\.([^.]+)\z/;
            printf " %2d. [%s] %s  (%s; %s folder)\n",
                $i + 1, uc($extension // 'file'),
                $c->{filename}, $label, $c->{directory};
        }
    }
    else {
        print " (no unattached matching files found)\n";
    }
    print " Scan warning: $_\n" for @$scan_issues;
    print "\nDefault MP3 folder: $SONG_AUDIO_DIR\n";
    print "Default TXT/PDF/ODT/JPG/PNG folder: $SONG_TAB_DIR\n";
    print "Unlimited MP3s and other files per song/Scales/Ear training/Theory; MP3s form a VLC playlist.\n";
    print "oN opens one; o2 o4 o5 (or o2,o4,o5) opens selected items; o opens ALL.\n";
    print "Enter candidate number(s) (e.g. 1,3 or all) to approve,\n";
    print "or filename/full path; -N removes attached item N; - clears all; Enter cancels: ";
    my $raw = <STDIN>;
    if (defined $raw) {
        chomp $raw;
        $raw = trim_text($raw);
        $raw = $1 if $raw =~ /^"(.*)"$/;
        if ($raw eq '') {
            $last_message = 'Media unchanged.';
        }
        elsif (lc($raw) eq 'o') {
            $last_message = open_all_attached_media($material_id);
        }
        elsif ($raw =~ /^o[\d\s,]/i) {
            my ($indices, $issue) = parse_attached_media_open_selection($raw, \@items);
            $last_message = defined($issue) ? $issue
                : open_selected_attached_media([ @items[@$indices] ]);
        }
        elsif ($raw =~ /^(?:all|\d+(?:\s*,\s*\d+)*)\z/i) {
            my ($approved, $issue) = parse_media_candidate_selection($raw, $candidates);
            $last_message = defined($issue) ? $issue
                : add_approved_media_candidates($material_id, $material_title,
                    $approved, $audio, $tabs);
        }
        elsif ($raw eq '-' || $raw =~ /^-\d+\z/) {
            if ($raw eq '-') {
                my $had_mp3 = @{ $audio->{$material_id} // [] } ? 1 : 0;
                my $had_tabs = @{ $tabs->{$material_id} // [] } ? 1 : 0;
                if (!$had_mp3 && !$had_tabs) {
                    $last_message = 'No attachments to remove.';
                }
                else {
                    my @errors;
                    if ($had_mp3) {
                        delete $audio->{$material_id};
                        my ($ok, $msg) = save_song_audio($audio);
                        push @errors, $msg unless $ok;
                    }
                    if ($had_tabs) {
                        delete $tabs->{$material_id};
                        my ($ok, $msg) = save_song_tabs($tabs);
                        push @errors, $msg unless $ok;
                    }
                    $last_message = @errors ? join(' ', @errors)
                        : "Removed all media for $material_title.";
                }
            }
            else {
                my $index = substr($raw, 1) - 1;
                if ($index < 0 || $index > $#items) {
                    $last_message = 'No attachment has that number.';
                }
                else {
                    my $item = $items[$index];
                    my ($ok, $msg);
                    if ($item->{kind} eq 'mp3') {
                        my $list = $audio->{$material_id};
                        splice(@$list, $item->{source_index}, 1);
                        delete $audio->{$material_id} unless @$list;
                        ($ok, $msg) = save_song_audio($audio);
                    }
                    else {
                        my $list = $tabs->{$material_id};
                        splice(@$list, $item->{source_index}, 1);
                        delete $tabs->{$material_id} unless @$list;
                        ($ok, $msg) = save_song_tabs($tabs);
                    }
                    $last_message = $ok ? "Removed attachment: $item->{path}" : $msg;
                }
            }
        }
        elsif ($raw =~ /[\t\r\n]/) {
            $last_message = 'File path may not contain tabs or line breaks.';
        }
        else {
            my ($kind, $file) = resolve_media_attachment_path($raw);
            if (!defined $kind) {
                $last_message = 'Supported files: .mp3, .txt, .pdf, .odt, .jpg, .jpeg, .png.';
            }
            elsif (!-f $file) {
                $last_message = "File not found: $file";
            }
            elsif ($kind eq 'mp3') {
                my $list = $audio->{$material_id} // [];
                if (grep { lc($_) eq lc($file) } @$list) {
                    $last_message = 'That MP3 is already attached.';
                }
                else {
                    push @$list, $file;
                    $audio->{$material_id} = $list;
                    my ($ok, $msg) = save_song_audio($audio);
                    $last_message = $ok
                        ? 'Attached MP3 to ' . $material_title . '. ' . open_song_in_vlc($material_id)
                        : $msg;
                }
            }
            else {
                my $list = $tabs->{$material_id} // [];
                if (grep { lc($_) eq lc($file) } @$list) {
                    $last_message = 'That file is already attached.';
                }
                else {
                    push @$list, $file;
                    $tabs->{$material_id} = $list;
                    my ($ok, $msg) = save_song_tabs($tabs);
                    $last_message = $ok
                        ? "Attached to $material_title. " . open_one_song_material($file)
                        : $msg;
                }
            }
        }
    }
    else {
        $last_message = 'Media unchanged.';
    }
    ReadMode('cbreak');
    $last_tick = time;  # Never count time in this menu as practice.
}

# Open an attached MP3 in Audacity for a song, Scales, Ear training, or Theory.
# Unlike selecting a practice song, this does not change playback or modify
# practice statistics. VLC keeps its own playlist; Audacity opens one chosen MP3.
sub prompt_edit_current_mp3 {
    my ($id, $title) = current_material_owner();
    if (!defined $id) {
        $last_message = 'Select a song (P/f), Scales (s), Ear training (h), or Theory (y), then press e(d) to edit its MP3.';
        return;
    }

    my $audio = read_song_audio();
    my @files = sort {
        media_sort_filename($a) cmp media_sort_filename($b)
            || lc($a) cmp lc($b)
            || $a cmp $b
    } @{ $audio->{$id} // [] };
    if (!@files) {
        $last_message = "No MP3 is attached to $title. Add one with t(k) first.";
        return;
    }

    my $file;
    if (@files == 1) {
        $file = $files[0];
    }
    else {
        ReadMode('restore');
        clear_screen();
        print "EDIT MP3 IN AUDACITY - $title\n";
        print "==============================\n\n";
        for my $i (0 .. $#files) {
            my $missing = -f $files[$i] ? '' : ' [FILE NOT FOUND]';
            printf " %2d. %s%s\n", $i + 1, $files[$i], $missing;
        }
        print "\nMP3 number to edit (Enter cancels): ";
        my $choice = <STDIN>;
        ReadMode('cbreak');
        $last_tick = time;  # No practice credit for time spent choosing.
        if (!defined $choice || $choice =~ /^\s*$/) {
            $last_message = 'Audacity opening canceled.';
            return;
        }
        $choice =~ s/^\s+|\s+\z//g;
        if ($choice !~ /\A\d+\z/ || $choice < 1 || $choice > @files) {
            $last_message = 'Invalid MP3 number. Nothing opened.';
            return;
        }
        $file = $files[$choice - 1];
    }

    if (!-f $file) {
        $last_message = "MP3 file not found: $file";
        return;
    }
    my ($audacity, $issue) = audacity_program();
    if (defined $issue) {
        $last_message = $issue;
        return;
    }
    my $err = launch_song_material_program($audacity, $file);
    $last_message = length($err) ? $err : "Sent MP3 to Audacity for editing: $file";
}

# Parse the "Some" prompt's attached-media numbers. Plain numbers are used
# here ("1 3 5", "1,3,5", or mixed); the media management menu continues
# to use "o1 o3 o5". Validate ALL selections before opening any files.
sub parse_media_load_some_selection {
    my ($input, $items) = @_;
    $input = trim_text($input // '');
    return (undef, 'No attachments selected.') unless length $input;
    return (undef, 'Enter attachment numbers separated by spaces or commas (e.g. 1 3 5).')
        unless $input =~ /\A[1-9]\d*(?:[\s,]+[1-9]\d*)*\z/;
    my %seen;
    my @indices;
    for my $number (split /[\s,]+/, $input) {
        return (undef, "Attachment number is too long: $number") if length($number) > 8;
        my $index = $number - 1;
        return (undef, "No attached media has number $number. Nothing opened.")
            if $index > $#$items;
        push @indices, $index unless $seen{$index}++;
    }
    return (\@indices, undef);
}

# Every initial media offer (Find, repertoire selection, tip song, Scales,
# Ear training and Theory) shares this prompt. Default is NONE; ALL uses
# the existing media launcher; SOME opens only numbered attached items.
# No choice here modifies attachments, practice time, or song selections.
sub offer_song_media_on_selection {
    my ($id) = @_;
    my $audio = read_song_audio();
    my $tabs  = read_song_tabs();
    my @items = media_entries_for_owner($id, $audio, $tabs);
    return '' unless @items;

    # A dashboard frame is drawn with direct-position writes, which do not
    # advance the Win32 cursor. Printing a prompt without clearing first can
    # therefore put its text and cursor ON TOP of the top dashboard rows.
    # Give the media question its own clean input screen; the next main-screen
    # render will do a complete repaint (and hide the idle text cursor).
    clear_screen();
    print "MEDIA SELECTION\n===============\n";
    while (1) {
        print "\nLoad associated media? 0=None  1=All  2=Some [Enter=0]: ";
        my $answer = <STDIN>;
        return '' unless defined $answer;
        $answer = trim_text($answer);
        return '' if $answer eq '' || $answer eq '0';
        return open_all_attached_media($id) if $answer eq '1';
        if ($answer eq '2') {
            print "\nAttached media:\n";
            for my $i (0 .. $#items) {
                my $path = $items[$i]{path};
                my $kind = $items[$i]{kind} eq 'mp3' ? 'MP3'
                    : ($path =~ /\.([^.\\\/]+)\z/ ? uc($1) : 'FILE');
                printf "  %2d. %-4s %s\n", $i + 1, $kind, $path;
            }
            while (1) {
                print "\nOpen which? (e.g. 1 3 5 or 1,3,5; Enter cancels): ";
                my $choice = <STDIN>;
                return '' unless defined($choice) && length(trim_text($choice));
                my ($indices, $error) = parse_media_load_some_selection($choice, \@items);
                if (defined $error) {
                    print "$error\n";
                    next;
                }
                return open_selected_attached_media([ @items[@$indices] ]);
            }
        }
        print "Please choose 0 (none), 1 (all), or 2 (some).\n";
    }
}

# All song-selection paths share this routine. Selecting a record changes
# both the category timer and the per-song timer and creates one selection
# count. The caller manages the timeline/menu boundary.
sub start_practicing_song_record {
    my ($record) = @_;
    return (0, 'That song is archived. Restore it in the song list before practicing it.')
        if $record->{archived};
    my $practice_key = "" . $record->{level};

    return (0, "Level $record->{level} is not a selectable practice timer level.")
        unless exists $by_key{$practice_key}
            && !$by_key{$practice_key}->{is_pause}
            && !$by_key{$practice_key}->{is_adjust}
            && !$by_key{$practice_key}->{is_scales}
            && !$by_key{$practice_key}->{is_ear_training};

    clear_resume_selection(); # A fresh Find/category song overrides suspended work.
    $current_key = $practice_key;
    $current_song_id = $record->{song_id};
    $current_song_title = $record->{title};
    # Selecting a song is provisional; do not count a start or accrue song
    # totals until 60 seconds have actually been played in this selection.
    $song_titles{$current_song_id} = $current_song_title;
    $current_selection_seconds = 0;
    $current_selection_qualified = 0;
    $current_selection_id = ++$selection_serial;
    $undo_locked = 0;  # A new song selection enables one fresh undo.
    $last_message =
        "Practicing [$record->{level} $record->{number}] $record->{title} " .
        "as [$practice_key] $by_key{$practice_key}->{name}.";
    my $media_message = offer_song_media_on_selection($current_song_id);
    $last_message .= " $media_message" if length $media_message;

    return (1, $last_message);
}

sub practice_song_category_entry {
    my ($records) = @_;
    my ($record, $err) = prompt_song_reference(
        "Song to practice, as level and song number, e.g. 2 3 or 2,3: ",
        $records,
    );
    return (0, $err) if defined $err;
    return start_practicing_song_record($record);
}

# Launch the exact song ID currently visible in the practice tip. This
# deliberately uses start_practicing_song_record(), the SAME entry point as
# Find and the category song list (including the default-None media question,
# provisional 60-second selection, category selection, and timeline logic).
# A reminder or a non-song tip never has a launchable song ID.
sub practice_displayed_tip_song {
    my ($song_id) = @_;
    if (!defined $song_id || $song_id eq '') {
        $last_message = 'No song recommendation is currently displayed.';
        return 0;
    }

    ReadMode('restore');
    my ($records, $warnings, $ids_changed) =
        read_song_categories_tsv($SONG_CATEGORY_FILE);
    if (!defined $records) {
        $last_message = "Cannot load recommended song: $SONG_CATEGORY_FILE not found or unreadable.";
        ReadMode('cbreak');
        $last_tick = time;
        return 0;
    }
    if ($ids_changed) {
        my ($ok, $message) = write_song_categories_tsv($records, $SONG_CATEGORY_FILE);
        unless ($ok) {
            $last_message = "Cannot save generated song IDs: $message";
            ReadMode('cbreak');
            $last_tick = time;
            return 0;
        }
    }

    my ($record) = grep { !$_->{archived} && $_->{song_id} eq $song_id } @$records;
    if (!$record) {
        $last_message = 'The recommended song is no longer in the catalog.';
        ReadMode('cbreak');
        $last_tick = time;
        return 0;
    }

    my ($ok, $message) = start_practicing_song_record($record);
    $last_message = $message;
    ReadMode('cbreak');
    $last_tick = time; # Do not count media-confirmation time as practice.
    return $ok;
}

# A quick song finder. Exact IDs/titles take priority; then ordinary
# case-insensitive title fragments; finally ordered word matches, including
# one-character spelling differences in longer words ("sliding" finds
# "slidin'", for example). We never guess if multiple songs match.
sub normalized_song_search {
    my ($value) = @_;
    $value = lc trim_text($value);
    $value =~ s/['\x{2019}]//g;
    $value =~ s/[^a-z0-9]+/ /g;
    return trim_text($value);
}

sub song_search_word_matches {
    my ($wanted, $actual) = @_;
    return 1 if index($actual, $wanted) == 0;
    return 0 if length($wanted) < 5 || length($actual) < 4;
    return 0 if abs(length($wanted) - length($actual)) > 1;

    # At most one insertion, deletion, or substitution. Avoid a broad
    # edit-distance algorithm so short fragments remain predictable.
    my ($i, $j, $errors) = (0, 0, 0);
    while ($i < length($wanted) && $j < length($actual)) {
        if (substr($wanted, $i, 1) eq substr($actual, $j, 1)) {
            $i++; $j++;
            next;
        }
        return 0 if ++$errors > 1;
        if (length($wanted) > length($actual)) { $i++; }
        elsif (length($wanted) < length($actual)) { $j++; }
        else { $i++; $j++; }
    }
    $errors += (length($wanted) - $i) + (length($actual) - $j);
    return $errors <= 1;
}

sub song_search_ordered_words_match {
    my ($query, $title) = @_;
    my @wanted = split / +/, $query;
    my @words = split / +/, $title;
    return 0 unless @wanted && @words;
    my $next = 0;
    for my $part (@wanted) {
        my $found = 0;
        for (; $next < @words; $next++) {
            if (song_search_word_matches($part, $words[$next])) {
                $next++;
                $found = 1;
                last;
            }
        }
        return 0 unless $found;
    }
    return 1;
}

sub search_song_records {
    my ($records, $raw_query) = @_;
    my $query = normalized_song_search($raw_query);
    return () unless length $query;

    # Do not treat an exact reference as ambiguous just because another
    # song happens to contain those words in a longer title.
    my @exact = grep {
        !$_->{archived} && (lc($_->{song_id} // '') eq lc(trim_text($raw_query))
            || lc($_->{title}) eq lc(trim_text($raw_query))
            || normalized_song_search($_->{title}) eq $query)
    } @$records;
    return @exact if @exact;

    my @fragments = grep {
        !$_->{archived} && (index(normalized_song_search($_->{title}), $query) >= 0
            || index(lc($_->{song_id} // ''), lc(trim_text($raw_query))) >= 0)
    } @$records;
    return @fragments if @fragments;

    return grep {
        !$_->{archived}
            && song_search_ordered_words_match($query, normalized_song_search($_->{title}))
    } @$records;
}

# The ordinary Find screen is an alphabetical, numbered repertoire index.
# Column-major ordering makes the full index easy to scan from A to Z.
# Archived songs are not included.  A number always refers to the same song
# in the complete alphabetical index, even when the list is filtered.
sub alphabetical_repertoire {
    my ($records) = @_;
    return sort {
        lc($a->{title}) cmp lc($b->{title})
            || $a->{title} cmp $b->{title}
            || ($a->{song_id} // '') cmp ($b->{song_id} // '')
    } grep { !$_->{archived} } @$records;
}

# Return a one-screen table (or a useful capacity error, never a partial table).
# $items contains [permanent_display_number, song_record] pairs.
# Width and height are the VISIBLE console dimensions, not the scrollback size.
sub format_find_repertoire_index {
    my ($items, $width, $height) = @_;
    $width  = int($width  // 0);
    $height = int($height // 0);
    return (undef, 'Cannot determine console dimensions. Resize/open Command Prompt and retry Find.')
        if $width < 1 || $height < 1;
    return (undef, "Find needs a wider console (at least 76 columns; currently $width).")
        if $width < 76;

    # Header, explanatory line, blank lines, optional feedback, and the prompt
    # occupy nine lines.  Leave another line as a Windows bottom-row margin.
    my $available_rows = $height - 10;
    return (undef, "Find needs a taller console window (currently $height lines).")
        if $available_rows < 1;

    my $number_width = length($items->[-1][0] // 1);
    my @entries = map { sprintf('%*d. %s',
        $number_width, $_->[0], $_->[1]{title}) } @$items;
    my $count = @entries;
    return ('(No active songs in your repertoire.)', undef) unless $count;

    my $max_columns = $count < 2 ? 1 : $count;
    # Prefer three columns when possible.  Two or more columns are used for
    # normal repertoires, but a long song name must never be clipped or wrapped.
    my @candidates = ($count >= 3 ? (3) : ());
    push @candidates, (2 .. $max_columns);
    push @candidates, 1 if $count == 1;
    my %seen;
    @candidates = grep { !$seen{$_}++ } @candidates;

    my ($chosen_columns, $chosen_rows, @chosen_widths);
    for my $columns (@candidates) {
        my $rows = int(($count + $columns - 1) / $columns);
        next if $rows > $available_rows;
        my @column_widths;
        for my $col (0 .. $columns - 1) {
            my $widest = 0;
            for my $row (0 .. $rows - 1) {
                my $idx = $col * $rows + $row;
                next if $idx >= $count;
                my $len = length($entries[$idx]);
                $widest = $len if $len > $widest;
            }
            push @column_widths, $widest;
        }
        my $total_width = 0;
        $total_width += $_ for @column_widths;
        $total_width += 3 * ($columns - 1);
        next if $total_width > $width;
        ($chosen_columns, $chosen_rows, @chosen_widths) =
            ($columns, $rows, @column_widths);
        last;
    }
    if (!defined $chosen_columns) {
        return (undef, "ERROR: $count songs cannot fit on one ${width}-column x ${height}-line screen without wrapping. Enlarge the Command Prompt window or reduce its font size; Find will not hide any songs.");
    }

    my @lines;
    for my $row (0 .. $chosen_rows - 1) {
        my @cells;
        for my $col (0 .. $chosen_columns - 1) {
            my $idx = $col * $chosen_rows + $row;
            next if $idx >= $count;
            my $cell = $entries[$idx];
            # Do not add trailing spaces to the final visible column.
            if ($col < $chosen_columns - 1
                && ($col + 1) * $chosen_rows + $row < $count) {
                $cell .= ' ' x ($chosen_widths[$col] - length($cell));
            }
            push @cells, $cell;
        }
        push @lines, join('   ', @cells);
    }
    return (join("\n", @lines), undef);
}

sub find_console_size {
    my ($width, $height);
    eval {
        ($width, $height) = GetTerminalSize(*STDOUT);
        1;
    };
    # Windows Command Prompt can sometimes return no size from ReadKey.
    # `mode con` reports the visible console's Columns and Lines instead.
    if ((!$width || !$height) && $^O eq 'MSWin32') {
        my $output = qx{mode con 2>NUL};
        ($width) = $output =~ /Columns:\s*(\d+)/i unless $width;
        ($height) = $output =~ /Lines:\s*(\d+)/i unless $height;
    }
    return ($width, $height);
}

sub prompt_song_search {
    ReadMode('restore');
    my ($records, $warnings, $ids_changed) = read_song_categories_tsv($SONG_CATEGORY_FILE);
    if (!defined $records) {
        $last_message = "Song search unavailable: $SONG_CATEGORY_FILE not found or unreadable.";
        clear_screen();
        print "$last_message\nPress Enter to return...";
        scalar <STDIN>;
        ReadMode('cbreak');
        $last_tick = time;
        return 0;
    }
    if ($ids_changed) {
        my ($ok, $message) = write_song_categories_tsv($records, $SONG_CATEGORY_FILE);
        unless ($ok) {
            $last_message = "Cannot save generated song IDs: $message";
            clear_screen();
            print "$last_message\nPress Enter to return...";
            scalar <STDIN>;
            ReadMode('cbreak');
            $last_tick = time;
            return 0;
        }
    }

    my @songs = alphabetical_repertoire($records);
    my @numbered = map { [$_ + 1, $songs[$_]] } 0 .. $#songs;
    my @visible = @numbered;
    my $feedback = '';
    my $capacity_error = '';
    while (1) {
        my ($width, $height) = find_console_size();
        my ($table, $error) = format_find_repertoire_index(\@visible, $width, $height);
        clear_screen();
        print "Find a Song to Practice\n=======================\n";
        print "\n";
        print scalar(@songs) . " active songs, alphabetical. Choose a number or search by title/ID.\n";
        print "\n";
        if (defined $error) {
            print "$error\n\n";
            print "Press Enter to return...";
            scalar <STDIN>;
            $capacity_error = $error;
            last;
        }
        print "$table\n\n";
        print "Enter a number to practice; type text to search; 'all' to show all.\n";
        print "$feedback\n";
        print "Song number / search (Enter cancels): ";
        my $query = <STDIN>;
        last unless defined $query;
        chomp $query;
        $query = trim_text($query);
        last unless length($query);

        if ($query =~ /^\d+$/) {
            my $number = 0 + $query;
            if ($number >= 1 && $number <= @songs) {
                my ($ok, $message) = start_practicing_song_record($songs[$number - 1]);
                $last_message = $message;
                ReadMode('cbreak');
                $last_tick = time; # Don't count the media question as practice.
                return $ok;
            }
            $feedback = "No repertoire song numbered $query (valid: 1-" . scalar(@songs) . ').';
            next;
        }
        if (lc($query) eq 'all') {
            @visible = @numbered;
            $feedback = '';
            next;
        }
        my @matches = search_song_records($records, $query);
        my %matches_by_id = map { $_->{song_id} => 1 } @matches;
        @visible = grep { $matches_by_id{ $_->[1]{song_id} } } @numbered;
        if (!@visible) {
            @visible = @numbered;
            $feedback = "No song matched '$query'; showing the full repertoire.";
            next;
        }
        if (@visible == 1) {
            my ($ok, $message) = start_practicing_song_record($visible[0][1]);
            $last_message = $message;
            ReadMode('cbreak');
            $last_tick = time;
            return $ok;
        }
        $feedback = scalar(@visible) . " matches for '$query' (original index numbers preserved).";
    }
    $last_message = length($capacity_error) ? $capacity_error
        : 'Song search canceled; previous practice selection unchanged.';
    ReadMode('cbreak');
    $last_tick = time;
    return 0;
}

# Read-only catalog search for the Category actions screen. Unlike the main
# Find-to-practice command, this is a LOOKUP: it never changes the active song.
# Include archived records here because this is an administrative menu, but
# explicitly flag them as unselectable; ordinary Find and tips still hide them.
sub find_category_song_matches {
    my ($records, $raw_query) = @_;
    my $query = normalized_song_search($raw_query);
    return () unless length($query);

    my @matches = grep {
        my $title = normalized_song_search($_->{title});
        my $id = normalized_song_search($_->{song_id} // '');
        index($title, $query) >= 0 || index($id, $query) >= 0
    } @$records;

    # Retain the familiar forgiving word matching from the main Find screen
    # when there are no direct title/ID substring matches.
    if (!@matches) {
        @matches = grep {
            song_search_ordered_words_match($query, normalized_song_search($_->{title}))
        } @$records;
    }

    return sort {
        ($a->{archived} // 0) <=> ($b->{archived} // 0)
            || $a->{level} <=> $b->{level}
            || $a->{number} <=> $b->{number}
            || lc($a->{title}) cmp lc($b->{title})
    } @matches;
}

# The summary uses the same historical last-snapshot rule as the activity
# report, plus dated corrections. The CURRENT in-memory session replaces its
# saved snapshot (if any), avoiding double counting after Save or View.
sub category_find_practice_stats {
    my ($wanted_ids) = @_;
    my %stats;
    return \%stats unless %$wanted_ids;

    my $valid = valid_logged_sessions();
    my ($latest) = read_song_log_for_report($SONG_LOG_FILE, $valid);
    for my $snapshot (values %$latest) {
        my $id = $snapshot->{id};
        next unless $wanted_ids->{$id} && statistics_include_date($snapshot->{session});
        next if defined($session_start_stamp)
            && $snapshot->{session} eq $session_start_stamp;
        $stats{$id}{seconds} += $snapshot->{seconds};
        my $last = $snapshot->{last} || $snapshot->{saved} || '';
        $stats{$id}{last} = $last
            if length($last) && (!$stats{$id}{last} || $last gt $stats{$id}{last});
    }

    my ($adjustments) = read_song_adjustment_log($SONG_ADJUST_FILE);
    for my $entry (@$adjustments) {
        my $id = $entry->{id};
        next unless $wanted_ids->{$id} && statistics_include_date($entry->{date});
        $stats{$id}{seconds} += $entry->{seconds};
        my $last = $entry->{date};
        $stats{$id}{last} = $last
            if length($last) && (!$stats{$id}{last} || $last gt $stats{$id}{last});
    }

    # Account for a session in progress, whether already saved or not.
    if (statistics_include_date($session_start_stamp // '')) {
        for my $id (keys %$wanted_ids) {
            my $seconds = $song_elapsed{$id} // 0;
            $stats{$id}{seconds} += $seconds;
            my $epoch = $song_last_practiced_epoch{$id} // 0;
            if ($seconds > 0 && $epoch > 0) {
                my $last = fmt_stamp($epoch);
                $stats{$id}{last} = $last
                    if !$stats{$id}{last} || $last gt $stats{$id}{last};
            }
        }
    }
    return \%stats;
}

sub find_song_in_category_menu {
    my ($records, $sheet_records) = @_;

    print "\nFIND IN SONG CATALOG\n";
    print "Search by title or permanent song ID. Archived songs are marked.\n";
    print "Search string [Enter to cancel]: ";
    my $input = <STDIN>;
    return 'Catalog Find canceled.' unless defined $input;
    my $query = trim_text($input);
    return 'Catalog Find canceled.' unless length($query);

    my @matches = find_category_song_matches($records, $query);
    my $out = "FIND RESULTS: $query\n" . ('-' x (14 + length($query))) . "\n";
    if (!@matches) {
        $out .= "No matching songs. Try another search from the Category actions menu.\n";
        print_paged_song_categories($out);
        return "No matches for '$query'.";
    }

    my %ids = map { ($_->{song_id} // '') => 1 } @matches;
    my $stats = category_find_practice_stats(\%ids);
    my $audio = read_song_audio();
    my $tabs = read_song_tabs();
    my $sheet_counts = sheet_music_count_by_song_id($sheet_records // []);
    my ($attributes, $attr_error) = read_song_attributes();
    $attributes //= {};

    $out .= scalar(@matches) . ' match' . (@matches == 1 ? '' : 'es') . "\n\n";
    for my $i (0 .. $#matches) {
        my $song = $matches[$i];
        my $id = $song->{song_id} // '';
        my $level = $song->{level};
        my $number = $song->{number};
        my $archived = $song->{archived} ? '  [ARCHIVED - not selectable]' : '';
        $out .= sprintf("%2d. [%d %d] %s%s\n", $i + 1,
            $level, $number, $song->{title}, $archived);
        $out .= '    Category: ' . level_label($level) . "\n";
        $out .= "    ID: $id\n";
        my @song_flags = grep { song_has_attribute($attributes, $id, $_) }
            qw(Memorized Emphasize);
        $out .= '    Attributes: ' . join(', ', @song_flags) . "\n" if @song_flags;
        my $total = $stats->{$id}{seconds} // 0;
        $total = 0 if $total < 0;
        $out .= '    Practice: ' . fmt_time($total)
            . '  |  Last: ' . ($stats->{$id}{last} || 'not recorded') . "\n";
        $out .= sprintf("    Media: %d MP3, %d tab/document, %d sheet file(s)\n",
            scalar(@{ $audio->{$id} // [] }),
            scalar(@{ $tabs->{$id} // [] }),
            ($sheet_counts->{$id} // 0));
        $out .= "    Archived reference is historical; use u to restore before practicing.\n"
            if $song->{archived};
        $out .= "\n";
    }
    $out .= "Numbers in brackets are category and song position, e.g. [6 1].\n";
    $out .= "Practice includes saved history, dated corrections, and this session"
        . ($STATISTICS_START_DATE eq '' ? ' (all dates).' : " since $STATISTICS_START_DATE.") . "\n";
    $out .= "Catalog Find does not change your active practice selection.\n";
    print_paged_song_categories($out);
    return "Found " . scalar(@matches) . " catalog match(es) for '$query'.";
}

sub show_song_categories {
    ReadMode('restore');

    my $message = '';

    while (1) {
        clear_screen();

        my ($records, $warnings, $ids_changed) = read_song_categories_tsv($SONG_CATEGORY_FILE);

        if (!defined $records) {
            print "Song Categories\n";
            print "===============\n\n";
            print join("\n", @$warnings), "\n\n";
            print "Create $SONG_CATEGORY_FILE in the same directory as this script.\n\n";
            print "Press Enter to return to the timer...";
            scalar <STDIN>;
            last;
        }

        if ($ids_changed) {
            my ($id_ok, $id_msg) = write_song_categories_tsv($records, $SONG_CATEGORY_FILE);
            $message = $id_ok
                ? "Upgraded song category rows with stable song IDs. $id_msg"
                : $id_msg;
        }

        my ($sheet_records, $sheet_warnings) = read_sheet_music_tsv($SHEET_MUSIC_FILE);
        push @$warnings, @$sheet_warnings if @$sheet_warnings;

        # Buffer the entire listing, then show at most 33 lines per page.
        print_paged_song_categories(format_song_categories($records, $warnings, $sheet_records));

        print "Message: $message\n\n" if length $message;
        print "Choose category action: ";
        chomp(my $choice = <STDIN>);
        $choice = lc trim_text($choice);

        if ($choice eq '') {
            last;
        }
        elsif ($choice eq 'f') {
            $message = find_song_in_category_menu($records, $sheet_records);
            prompt_to_continue();
        }
        elsif ($choice eq 'd') {
            $message = archive_song_category_entry($records);
            prompt_to_continue();
        }
        elsif ($choice eq 'x') {
            $message = delete_song_category_entry($records);
            prompt_to_continue();
        }
        elsif ($choice eq 'u') {
            $message = restore_archived_song_category_entry($records);
            prompt_to_continue();
        }
        elsif ($choice eq 'a') {
            $message = add_song_category_entry($records);
            prompt_to_continue();
        }
        elsif ($choice eq 'm') {
            $message = move_song_category_entry($records);
            prompt_to_continue();
        }
        elsif ($choice eq 'n') {
            $message = rename_song_category_entry($records);
            prompt_to_continue();
        }
        elsif ($choice eq 'l') {
            $message = view_audit_log();
            prompt_to_continue();
        }
        elsif ($choice eq 's') {
            $message = manage_sheet_music_for_song($records);
            prompt_to_continue();
        }
        elsif ($choice eq 't') {
            my ($attributes_message, $practice_started) = manage_song_attributes($records);
            $message = $attributes_message;
            last if $practice_started;
        }
        elsif ($choice eq 'p') {
            my ($started, $practice_message) = practice_song_category_entry($records);
            $message = $practice_message;

            if ($started) {
                last;
            }

            prompt_to_continue();
        }
        else {
            $message = "Unknown category option '$choice'. Use p, f, s, t, d, x, u, a, m, n, l, or Enter.";
            prompt_to_continue();
        }
    }

    ReadMode('cbreak');

    # Prevent reading time from being added to the current category.
    $last_tick = time;
}

# Validate a signed number of minutes and convert it to whole seconds.
# Decimal minute values are supported (e.g. +12.5 and -3.25).
sub fmt_signed_time {
    my ($seconds) = @_;
    return ($seconds < 0 ? '-' : ($seconds > 0 ? '+' : ''))
        . fmt_time(abs($seconds));
}

sub parse_signed_minutes {
    my ($input) = @_;
    $input = trim_text($input);
    return (undef, 'Enter a signed number of minutes, such as +15, -2.5, or 30.')
        unless $input =~ /\A[+-]?(?:\d+(?:\.\d*)?|\.\d+)\z/;
    my $amount = 0 + $input;
    return (undef, 'Adjustment is too large (maximum 10,080 minutes per entry).')
        if abs($amount) > 10080;
    my $seconds = ($amount < 0 ? -1 : 1) * int(abs($amount) * 60 + 0.5);
    return (undef, 'Adjustment must be at least one second.') if !$seconds;
    return ($seconds, undef);
}

sub validate_practice_date {
    my ($input) = @_;
    $input = trim_text($input);
    return (undef, 'Use YYYY-MM-DD, for example 2026-11-06.')
        unless $input =~ /\A(\d{4})-(\d{2})-(\d{2})\z/;
    my ($year, $month, $day) = ($1, $2, $3);
    my $epoch = eval { timelocal(0, 0, 12, $day, $month - 1, $year) };
    return (undef, 'That is not a valid calendar date.')
        if $@ || !defined($epoch) || strftime('%Y-%m-%d', localtime($epoch)) ne $input;
    return (undef, 'Future practice dates are not allowed.')
        if $input gt strftime('%Y-%m-%d', localtime(time));
    return ($input, undef);
}

# Backdated entries are strictly tab-delimited; malformed entries are ignored,
# never silently treated as additional practice.
sub read_song_adjustment_log {
    my ($file) = @_;
    $file //= $SONG_ADJUST_FILE;
    my @entries;
    my $skipped = 0;
    return (\@entries, $skipped) unless -e $file;
    open my $fh, '<', $file or return (\@entries, 1);
    my $header = <$fh>;
    while (my $line = <$fh>) {
        chomp $line;
        $line =~ s/\r\z//;
        next if $line =~ /^\s*$/;
        my ($recorded, $date, $id, $title, $level, $delta, $sync, $note) = split /\t/, $line, -1;
        my ($valid_date) = validate_practice_date($date // '');
        if (!defined $valid_date || !defined($id) || !length($id)
            || !defined($level) || !valid_song_level($level)
            || !defined($delta) || $delta !~ /\A[+-]?(?:\d+(?:\.\d*)?|\.\d+)\z/
            || !defined($sync) || $sync !~ /\A[01]\z/
            || !defined($recorded) || $recorded !~ /^\d{4}-\d\d-\d\d /) {
            $skipped++;
            next;
        }
        push @entries, {
            recorded => $recorded, date => $date, id => $id, title => $title,
            level => 0 + $level, seconds => 0 + $delta, sync => 0 + $sync,
            note => $note // '',
        };
    }
    close $fh;
    return (\@entries, $skipped);
}

# All changes to the historical adjustment log are append-only; correcting an
# accidental entry means adding the opposite signed amount, not rewriting data.
sub append_song_adjustment {
    my ($entry) = @_;
    my $file = $SONG_ADJUST_FILE;
    my $new_file = !-e $file || -z $file;
    open my $fh, '>>', $file or return (0, "Could not write $file: $!");
    if ($new_file) {
        print $fh join("\t", qw(recorded_at practice_date song_id song_title
                                  category delta_seconds count_in_category note)), "\n";
    }
    my $note = $entry->{note} // '';
    $note =~ s/[\t\r\n]+/ /g;
    my $title = $entry->{title} // $entry->{id};
    $title =~ s/[\t\r\n]+/ /g;
    print $fh join("\t", fmt_stamp(time), $entry->{date}, $entry->{id},
        $title, $entry->{level}, $entry->{seconds}, $entry->{sync} ? 1 : 0,
        $note), "\n";
    close $fh or return (0, "Error closing $file: $!");
    return (1, "Saved dated adjustment in $file.");
}

# Retrieve only session IDs actually represented in the master activity log.
# Orphaned per-song snapshots must not be used to authorize a subtraction,
# because the report intentionally ignores them.
sub valid_logged_sessions {
    my %valid;
    return \%valid unless -e $LOG_FILE;
    open my $fh, '<', $LOG_FILE or return \%valid;
    my $header = <$fh>;
    while (my $line = <$fh>) {
        my ($session) = split /\t/, $line;
        my ($epoch) = parse_log_stamp($session // '');
        $valid{$session} = 1 if defined $epoch;
    }
    close $fh;
    return \%valid;
}

# Return the historical category balance for the specified date, combining
# last snapshots of timed sessions with all category-synced dated corrections.
sub category_seconds_on_date {
    my ($level, $practice_date, $entries) = @_;
    my %last_row;
    if (-e $LOG_FILE && open my $fh, '<', $LOG_FILE) {
        my $header = <$fh>;
        while (my $line = <$fh>) {
            chomp $line;
            $line =~ s/\r\z//;
            my @cols = split /\t/, $line, -1;
            my $day = date_from_stamp_text($cols[0] // '');
            next unless defined($day) && $day eq $practice_date;
            $last_row{$cols[0]} = \@cols;
        }
        close $fh;
    }
    my @opts = practice_options();
    my $total = 0;
    my $current_disk = 0;
    for my $session (keys %last_row) {
        my $parsed = parse_activity_log_row_for_report($last_row{$session}, \@opts);
        next unless defined $parsed;
        for my $i (0 .. $#opts) {
            next unless $opts[$i]->{key} eq "$level";
            my $seconds = $parsed->{category_seconds}->[$i] // 0;
            $total += $seconds;
            $current_disk = $seconds if $session eq $session_start_stamp;
            last;
        }
    }
    if (date_from_stamp_text($session_start_stamp // '') eq $practice_date) {
        $total += ($elapsed{"$level"} // 0) - $current_disk;
    }
    for my $entry (@$entries) {
        $total += $entry->{seconds}
            if $entry->{sync} && $entry->{date} eq $practice_date
            && "$entry->{level}" eq "$level";
    }
    return $total;
}

# Sum song practice for a chosen calendar day across timer snapshots and
# previously written dated corrections. Used to prevent negative day balances.
sub song_seconds_on_date {
    my ($song_id, $practice_date, $entries) = @_;
    my $valid_sessions = valid_logged_sessions();
    my ($snapshots) = read_song_log_for_report($SONG_LOG_FILE, $valid_sessions);
    my $seconds = 0;
    for my $snapshot (values %$snapshots) {
        next unless $snapshot->{id} eq $song_id;
        next unless date_from_stamp_text($snapshot->{session}) eq $practice_date;
        $seconds += $snapshot->{seconds};
    }
    for my $entry (@$entries) {
        next unless $entry->{id} eq $song_id && $entry->{date} eq $practice_date;
        $seconds += $entry->{seconds};
    }
    # A live session may have more recent time than its last disk snapshot.
    if (date_from_stamp_text($session_start_stamp // '') eq $practice_date
        && exists $song_elapsed{$song_id}) {
        my $on_disk = 0;
        for my $snapshot (values %$snapshots) {
            $on_disk = $snapshot->{seconds}
                if $snapshot->{id} eq $song_id
                && $snapshot->{session} eq $session_start_stamp;
        }
        $seconds += ($song_elapsed{$song_id} - $on_disk);
    }
    return $seconds;
}

# Quick song finder for Adjust. An unambiguous title fragment needs no
# separate selection step; a numbered chooser appears only for true ambiguity.
sub choose_song_for_adjustment {
    my ($records, $initial_query) = @_;
    my $query = $initial_query;

    while (1) {
        if (!defined $query) {
            print "Song name, level/number, or ID (l=list, Enter=cancel): ";
            $query = <STDIN>;
            return (undef, 'Canceled.') unless defined $query;
            chomp $query;
        }
        $query = trim_text($query);
        return (undef, 'Canceled.') unless length $query;

        if (lc($query) eq 'l') {
            my $grouped = group_song_categories_by_level($records);
            my $output = "Available songs (enter a title, level/number, or ID)\n";
            for my $level (sort { $a <=> $b } keys %$grouped) {
                $output .= "\n" . level_label($level) . "\n";
                for my $record (@{ $grouped->{$level} }) {
                    $output .= sprintf("%2d %2d  %-40.40s  %s\n", $level,
                        $record->{number}, $record->{title}, $record->{song_id});
                }
            }
            print_paged_song_categories($output);
            $query = undef;
            next;
        }

        my ($level, $number, $parse_err) = parse_song_ref($query);
        if (!defined $parse_err) {
            my $record = find_song_record($records, $level, $number);
            return ($record, undef) if $record;
            print "No song at [$level $number]. Try a title or Enter to cancel.\n";
            $query = undef;
            next;
        }

        my @matches = sort {
            $a->{level} <=> $b->{level}
                || $a->{number} <=> $b->{number}
                || lc($a->{title}) cmp lc($b->{title})
        } search_song_records($records, $query);
        return ($matches[0], undef) if @matches == 1;

        if (@matches > 1) {
            print "\nMore than one song matches '$query':\n";
            for my $i (0 .. $#matches) {
                printf "%2d. [%s %d] %s\n", $i + 1,
                    $matches[$i]->{level}, $matches[$i]->{number}, $matches[$i]->{title};
            }
            print "Choose 1-" . scalar(@matches) . " (Enter=cancel, r=refine): ";
            my $choice = <STDIN>;
            return (undef, 'Canceled.') unless defined $choice;
            chomp $choice;
            $choice = trim_text($choice);
            return (undef, 'Canceled.') if $choice eq '';
            if ($choice =~ /^\d+$/ && $choice >= 1 && $choice <= @matches) {
                return ($matches[$choice - 1], undef);
            }
            print "Search again.\n";
        }
        else {
            print "No song matches '$query'. Try another name.\n";
        }
        $query = undef;
    }
}

# Fast path: an ordinary adjustment is two prompts after pressing a:
# song title, then signed minutes. No mode/confirmation/category questions.
# Optional inline modifiers retain dated and song-only corrections:
#   -5                 current session, song + category
#   +12@2026-11-06     dated history, song + category
#   +5!                song total only, do not change category
#   +5@2026-11-06#2!  dated song-only correction, with category metadata
sub adjust_individual_song {
    my ($records, $record) = @_;
    my $song_id = $record->{song_id};
    my $song_level = $record->{level};
    my $category = $song_level;
    $category = $current_key if $current_song_id eq $song_id && valid_song_level($current_key);

    print "\n$record->{title}   (this session: " . fmt_time($song_elapsed{$song_id} // 0) . ")\n";
    print "Minutes [+/-] (e.g. +5, -2.5; \@YYYY-MM-DD for dated, ! for song only): ";
    my $input = <STDIN>;
    return 'Canceled.' unless defined $input;
    chomp $input;
    $input = trim_text($input);
    return 'Canceled.' unless length $input;

    my ($minutes, $date_text, $category_text, $song_only) =
        $input =~ /\A([+-]?(?:\d+(?:\.\d*)?|\.\d+))\s*(?:\@\s*(\d{4}-\d{2}-\d{2}))?\s*(?:\#([0-6]))?\s*(!)?\z/;
    return 'Invalid entry. Examples: +5, -2.5, +10@2026-11-06, +5!'
        unless defined $minutes;

    my ($delta, $minutes_err) = parse_signed_minutes($minutes);
    return $minutes_err if defined $minutes_err;

    my $dated = defined $date_text;
    my $date = '';
    if ($dated) {
        my ($valid_date, $date_err) = validate_practice_date($date_text);
        return $date_err if defined $date_err;
        $date = $valid_date;
    }
    $category = $category_text if defined $category_text;
    my $sync = !$song_only;

    my ($entries) = read_song_adjustment_log($SONG_ADJUST_FILE);
    my $old_seconds = $dated
        ? song_seconds_on_date($song_id, $date, $entries)
        : ($song_elapsed{$song_id} // 0);

    return "Cannot subtract more than the available " . fmt_time($old_seconds) .
        " for '$record->{title}' " . ($dated ? "on $date." : 'this session.')
        if $old_seconds + $delta < -0.01;

    if ($sync && $delta < 0 && !$dated && $elapsed{$category} + $delta < -0.01) {
        return 'Category has insufficient recorded time. Use a smaller subtraction'
            . ' or append ! for song-only correction.';
    }
    if ($sync && $delta < 0 && $dated) {
        my $available = category_seconds_on_date($category, $date, $entries);
        return "Category [$category] has only " . fmt_time($available) .
            " on $date. Use a smaller subtraction or append ! for song only."
            if $available + $delta < -0.01;
    }

    if (!$dated) {
        $song_elapsed{$song_id} = $old_seconds + $delta;
        $song_elapsed{$song_id} = 0 if $song_elapsed{$song_id} < 0.01;
        $song_titles{$song_id} = $record->{title};
        if ($delta > 0) {
            $song_last_practiced_epoch{$song_id} = time;
        }
        elsif ($song_elapsed{$song_id} == 0) {
            $song_last_practiced_epoch{$song_id} = 0;
        }
        if ($sync) {
            $elapsed{$category} += $delta;
            $elapsed{$category} = 0 if $elapsed{$category} < 0.01;
        }
        save_state();
        save_log();
        save_song_log();
        my $audit_note = audit_write({ action => 'PRACTICE_TIME_ADJUSTED',
            id => $song_id, old => fmt_time($old_seconds),
            new => fmt_time($song_elapsed{$song_id}),
            detail => "Song $record->{title}; delta " . fmt_signed_time($delta)
                . "; session $session_start_stamp; category $category; "
                . ($sync ? 'category included' : 'song only') });
        return "Adjusted '$record->{title}' " . fmt_signed_time($delta) .
            " | Session total: " . fmt_time($song_elapsed{$song_id}) .
            ($sync ? " | Category [$category] updated." : ' | Song only.') . $audit_note;
    }

    # Make historical corrections durable without requiring additional prompts.
    save_state();
    save_log();
    save_song_log();
    my ($ok, $message) = append_song_adjustment({
        date => $date, id => $song_id, title => $record->{title},
        level => $category, seconds => $delta, sync => $sync, note => '',
    });
    return $message unless $ok;
    my $audit_note = audit_write({ action => 'PRACTICE_TIME_ADJUSTED',
        id => $song_id, old => fmt_time($old_seconds),
        new => fmt_time($old_seconds + $delta),
        detail => "Song $record->{title}; date $date; delta " . fmt_signed_time($delta)
            . "; category $category; " . ($sync ? 'category included' : 'song only') });
    return "Adjusted '$record->{title}' on $date " . fmt_signed_time($delta) .
        " | Date total: " . fmt_time($old_seconds + $delta) .
        ($sync ? " | Category [$category] updated." : ' | Song only.') . $audit_note;
}

sub prompt_song_adjustment {
    my ($initial_query) = @_;
    my ($records, $warnings, $ids_changed) = read_song_categories_tsv($SONG_CATEGORY_FILE);
    return "No song list: $SONG_CATEGORY_FILE" unless defined $records;
    if ($ids_changed) {
        my ($ok, $message) = write_song_categories_tsv($records, $SONG_CATEGORY_FILE);
        return $message unless $ok;
    }
    my ($record, $err) = choose_song_for_adjustment($records, $initial_query);
    return $err if defined $err;
    return adjust_individual_song($records, $record);
}

sub prompt_adjustment {
    ReadMode('restore');
    clear_screen();

    print "Adjust Time\n===========\n\n";
    print "Category: 0-6, y (Theory), p (Pause), scales, or ear training (h)\n";
    print "Song: type a title fragment, ID, level/number (e.g. 4 2), or s to search\n";
    print "Enter=cancel\n\n";
    print "Category or song: ";
    my $raw = <STDIN>;
    unless (defined $raw) {
        $last_message = 'Adjustment canceled.';
        ReadMode('cbreak');
        $last_tick = time;
        return;
    }
    chomp $raw;
    my $choice = trim_text($raw);
    my $key = lc $choice;

    if ($choice eq '') {
        $last_message = 'Adjustment canceled.';
    }
    elsif ($key eq 's' || $key eq 'song' || $key eq 'l'
        || !exists($by_key{$key}) && $key ne 'scales'
           && $key ne 'ear' && $key ne 'ear training' && $key ne 'theory') {
        # A full or partial song title can be entered directly here, avoiding
        # the old extra 's' selector. Short 's' still opens song search.
        my $query = ($key eq 's' || $key eq 'song') ? undef : $choice;
        $last_message = prompt_song_adjustment($query);
    }
    else {
        my $adjust_key = $key eq 'scales' ? 's'
            : ($key eq 'ear' || $key eq 'ear training') ? 'h'
            : $key eq 'theory' ? 'y' : $key;
        if (!exists($by_key{$adjust_key}) || $by_key{$adjust_key}->{is_adjust}
            || $by_key{$adjust_key}->{is_retired}) {
            $last_message = "Invalid category '$choice'.";
        }
        else {
            print "Adjustment for $by_key{$adjust_key}->{name} in minutes (+/-): ";
            my $raw_minutes = <STDIN>;
            if (!defined $raw_minutes) {
                $last_message = 'Adjustment canceled.';
            }
            else {
                chomp $raw_minutes;
                my ($delta, $error) = parse_signed_minutes($raw_minutes);
                if (defined $error) {
                    $last_message = $error;
                }
                else {
                    my $old_total = $elapsed{$adjust_key};
                    $elapsed{$adjust_key} += $delta;
                    $elapsed{$adjust_key} = 0 if $elapsed{$adjust_key} < 0;
                    my $actual_delta = $elapsed{$adjust_key} - $old_total;
                    my $audit_note = $actual_delta != 0 ? audit_write({
                        action => 'PRACTICE_TIME_ADJUSTED', id => "\@$adjust_key",
                        old => fmt_time($old_total), new => fmt_time($elapsed{$adjust_key}),
                        detail => "Category $by_key{$adjust_key}->{name}; session $session_start_stamp; delta "
                            . fmt_signed_time($actual_delta) }) : '';
                    $last_message = "Adjusted $by_key{$adjust_key}->{name} " . fmt_signed_time($actual_delta)
                        . ". New total: " . fmt_time($elapsed{$adjust_key}) . $audit_note;
                }
            }
        }
    }

    ReadMode('cbreak');
    $last_tick = time; # No timer credit for the time spent in this menu.
}

sub prompt_session_start {
    ReadMode('restore');

    clear_screen();

    print "Set Session Start Time\n";
    print "======================\n\n";

    print "Current session start:\n";
    print "  $session_start_stamp\n\n";

    print "Enter the new session start time in this exact format:\n";
    print "  YYYY-MM-DD HH:MM:SS\n\n";

    print "Properly formatted example:\n";
    print "  2026-06-16 09:28:48\n\n";

    print "New session start time, or press Enter to cancel: ";
    chomp(my $input = <STDIN>);

    if ($input =~ /^\s*$/) {
        print "\nNo change made.\n";
        print "Press Enter to continue...";
        scalar <STDIN>;
        ReadMode('cbreak');
        $last_tick = time;
        return;
    }

    my ($epoch, $err) = parse_session_start($input);

    if (!defined $epoch) {
        print "\nInvalid session-start time.\n\n";
        print "$err\n\n";
        print "No change made.\n";
        print "Press Enter to continue...";
        scalar <STDIN>;
        ReadMode('cbreak');
        $last_tick = time;
        return;
    }

    $session_start       = $epoch;
    $session_start_stamp = fmt_stamp($session_start);

    # Make the displayed Session elapsed agree with the newly chosen start time.
    $session_elapsed_offset = time - $session_start;
    $session_elapsed_offset = 0 if $session_elapsed_offset < 0;
    $session_clock_anchor   = time;

    print "\nSession start changed to:\n";
    print "  $session_start_stamp\n\n";

    print "Elapsed category totals were not changed.\n";
    print "Use key a if you also need to adjust active or pause time.\n\n";

    print "Press Enter to continue...";
    scalar <STDIN>;

    ReadMode('cbreak');

    # Prevent time spent in this prompt from being added to the current timer.
    $last_tick = time;
}

# Add exactly one minute without changing the current selected activity,
# song, chronological segments or paused resume target. This is used by
# b(n) and F7 (Scales), and F6 (Theory). Every change is audit-logged.
sub bump_practice_minute {
    my ($key) = @_;
    return 'Invalid bump category.' unless $key eq 's' || $key eq 'y';
    my $category = $by_key{$key}->{name};
    my $old_total = $elapsed{$key};
    $elapsed{$key} += 60;
    my $media_id = $key eq 's' ? $SCALES_ATTACHMENT_ID : $THEORY_ATTACHMENT_ID;
    my $audit_note = audit_write({ action => 'PRACTICE_TIME_ADJUSTED',
        id => $media_id, old => fmt_time($old_total),
        new => fmt_time($elapsed{$key}),
        detail => "$category manual +1 minute; session $session_start_stamp" });
    return "Added 1 minute to $category. Total: " . fmt_time($elapsed{$key}) . $audit_note;
}

sub save_log {
    my $file = $LOG_FILE;
    my $stamp = strftime("%Y-%m-%d %H:%M:%S", localtime);
    my $pause_key = pause_key();
    my $scales_key = scales_key();
    my $ear_key = ear_training_key();

    my @practice_options = practice_options();

    my @elapsed_headers = map {
        'elapsed_' . log_name($_->{name})
    } @practice_options;

    my @pct_headers = map {
        'pct_' . log_name($_->{name})
    } @practice_options;

    my @elapsed_values = map {
        fmt_time($elapsed{ $_->{key} })
    } @practice_options;

    my @pct_values = map {
        $_->{key} eq 'y' ? '-' : sprintf("%.1f%%", percent_for($_->{key}))
    } @practice_options;

    my $need_header = (!-e $file || -z $file);

    open my $fh, '>>', $file
        or die "Could not write to $file: $!";

    if ($need_header) {
        my @headers = (
            'session_start',
            'saved_at',
            @elapsed_headers,
            'elapsed_pause',
            @pct_headers,
            'session_elapsed',
            'active_practice',
            'practice_session_pct',
            'current_key',
            'state_file',
            'elapsed_scales',
            'elapsed_ear_training',
            'daily_active_dates', # exact local-date breakdown for newer sessions
            'daily_theory_dates', # exact local-date Theory minutes for the daily target
        );

        print $fh join("\t", @headers), "\n";
    }

    my @values = (
        $session_start_stamp,
        $stamp,
        @elapsed_values,
        fmt_time($elapsed{$pause_key}),
        @pct_values,
        fmt_time(session_elapsed()),
        fmt_time(active_total()),
        sprintf("%.1f%%", practice_session_percent()),
        $current_key,
        $STATE_FILE,
        defined $scales_key ? fmt_time($elapsed{$scales_key}) : fmt_time(0),
        defined $ear_key ? fmt_time($elapsed{$ear_key}) : fmt_time(0),
        encode_practice_calendar_days(session_active_seconds_by_local_date()),
        encode_theory_calendar_days(session_theory_seconds_by_local_date()),
    );

    print $fh join("\t", @values), "\n";

    close $fh;
}

# Each row is a full cumulative snapshot for ONE song in ONE timer session.
# Saving mid-session (uppercase S), saving on exit, and reloading (/r) do not double count.
sub save_song_log {
    return unless keys %song_elapsed;

    my $file = $SONG_LOG_FILE;
    my $stamp = fmt_stamp(time);
    my $need_header = (!-e $file || -z $file);

    open my $fh, '>>', $file or die "Could not write to $file: $!";
    if ($need_header) {
        print $fh join("\t", qw(session_start saved_at song_id song_title
                                  elapsed_seconds practice_starts last_practiced_at)), "\n";
    }

    for my $song_id (sort keys %song_elapsed) {
        my $seconds = $song_elapsed{$song_id} // 0;
        # Zero is a valid replacement snapshot (e.g. an erroneous song entry
        # corrected back to zero). Never let an older nonzero save survive.
        my $last_epoch = $song_last_practiced_epoch{$song_id} // 0;
        my $last_stamp = $last_epoch > 0 ? fmt_stamp($last_epoch) : '';
        printf $fh "%s\t%s\t%s\t%s\t%.6f\t%d\t%s\n",
            $session_start_stamp, $stamp, $song_id,
            ($song_titles{$song_id} // $song_id), $seconds,
            ($song_practice_starts{$song_id} // 0), $last_stamp;
    }
    close $fh;
}

sub read_song_log_for_report {
    my ($file, $valid_sessions) = @_;
    my %latest;
    my $skipped = 0;
    my $updates = 0;
    return (\%latest, $skipped, $updates) unless -e $file;

    open my $fh, '<', $file or return (\%latest, 1, 0);
    my $header = <$fh>;
    while (my $line = <$fh>) {
        chomp $line;
        $line =~ s/\r\z//;
        next if $line =~ /^\s*$/;
        my ($session, $saved, $id, $title, $seconds, $starts, $last) = split /\t/, $line, -1;
        unless (defined $id && length $id && defined $seconds
            && $seconds =~ /\A(?:\d+(?:\.\d*)?|\.\d+)\z/
            && (!defined($valid_sessions) || exists $valid_sessions->{$session})) {
            $skipped++;
            next;
        }
        my $key = $session . "\0" . $id;
        $updates++ if exists $latest{$key};
        $latest{$key} = {
            session => $session,
            saved   => $saved,
            id      => $id,
            title   => $title,
            seconds => 0 + $seconds,
            starts  => (defined $starts && $starts =~ /^\d+$/) ? 0 + $starts : 0,
            last    => $last // '',
        };
    }
    close $fh;
    return (\%latest, $skipped, $updates);
}

sub print_song_stats_for_report {
    my ($out, $song_log, $valid_sessions) = @_;
    my ($snapshots, $skipped, $updates) = read_song_log_for_report($song_log, $valid_sessions);
    my %stats;
    my %timer_days;

    for my $snapshot (values %$snapshots) {
        my $seconds = $snapshot->{seconds};
        next unless $seconds > 0;
        my $id = $snapshot->{id};
        my $stat = ($stats{$id} //= {
            seconds => 0, sessions => 0, starts => 0,
            title => '', last => '', first => '',
        });
        $stat->{seconds} += $seconds;
        $stat->{sessions}++;
        $timer_days{$id . "\0" . (date_from_stamp_text($snapshot->{session}) // '')} = 1;
        $stat->{starts} += $snapshot->{starts};
        $stat->{title} = $snapshot->{title} if length($snapshot->{title} // '');
        my $practice_stamp = $snapshot->{last} || $snapshot->{saved};
        $stat->{last} = $practice_stamp
            if $practice_stamp && (!$stat->{last} || $practice_stamp gt $stat->{last});
        $stat->{first} = $snapshot->{session}
            if !$stat->{first} || $snapshot->{session} lt $stat->{first};
    }

    # Dated entries are deltas; they are NEVER included in timer snapshots.
    my ($all_manual_entries, $manual_skipped) = read_song_adjustment_log($SONG_ADJUST_FILE);
    my @filtered_manual_entries = grep { statistics_include_date($_->{date}) } @$all_manual_entries;
    my $manual_entries = \@filtered_manual_entries;
    my %manual_by_day;
    my $manual_category_seconds = 0;
    for my $entry (@$manual_entries) {
        my $id = $entry->{id};
        my $stat = ($stats{$id} //= {
            seconds => 0, sessions => 0, starts => 0,
            title => '', last => '', first => '',
        });
        $stat->{seconds} += $entry->{seconds};
        $stat->{manual_edits}++;
        $stat->{title} = $entry->{title} if length($entry->{title} // '');
        $manual_by_day{$id . "\0" . $entry->{date}} += $entry->{seconds};
        $manual_category_seconds += $entry->{seconds} if $entry->{sync};
    }
    for my $key (keys %manual_by_day) {
        my ($id, $date) = split /\0/, $key, 2;
        next unless $manual_by_day{$key} > 0.01;
        my $stat = $stats{$id};
        # A dated ad hoc practice day is a single additional session; it may
        # be distinct from any timer session recorded on the same day.
        $stat->{sessions}++;
        $stat->{last} = $date if !$stat->{last} || $date gt $stat->{last};
        $stat->{first} = $date if !$stat->{first} || $date lt $stat->{first};
    }

    # Current titles/categories are display metadata only; ID is the identity.
    my %current;
    my ($song_records) = read_song_categories_tsv($SONG_CATEGORY_FILE);
    if (defined $song_records) {
        for my $record (@$song_records) {
            $current{$record->{song_id}} = $record;
        }
    }

    my @ids = sort {
        $stats{$b}->{seconds} <=> $stats{$a}->{seconds} || $a cmp $b
    } grep { $stats{$_}->{seconds} > 0.01 } keys %stats;
    my $total = 0;
    $total += $stats{$_}->{seconds} for @ids;
    my $starts = 0;
    $starts += $stats{$_}->{starts} for @ids;

    print $out "\nIndividual song practice\n";
    print $out "------------------------\n";
    print $out "Source TSV: $song_log\n";
    print $out "Dated corrections TSV: $SONG_ADJUST_FILE\n";
    print $out "Dated adjustment entries: ".scalar(@$manual_entries)." (skipped: $manual_skipped)\n";
    print $out "Dated adjustment time credited to categories: ".fmt_signed_time($manual_category_seconds)."\n";
    print $out "Tracked song practice: " . fmt_time_decimal($total) . "\n";
    print $out "Distinct songs practiced: " . scalar(@ids) . "\n";
    print $out "Song practice selections: $starts\n";
    print $out "Replaced older per-song save snapshots: $updates\n";
    print $out "Skipped song log rows: $skipped\n";
    print $out "Only time explicitly assigned to a song is counted here. Backdated entries are combined by practice date.\n";
    print $out "Sessions include timer sessions and days with positive net dated entries; Starts counts timer song selections only.\n\n";

    if (!@ids) {
        print $out "No individual song practice has been recorded yet.\n";
        return;
    }

    printf $out "%-34s %-26s %12s %8s %8s %7s %12s %-19s %s\n",
        'Song', 'Current category', 'Total', 'Sessions', 'Starts', 'Dated', 'Avg/session', 'Last practiced', 'Song ID';
    print $out '-' x 160, "\n";
    for my $id (@ids) {
        my $stat = $stats{$id};
        my $song = $current{$id};
        my $title = $song ? $song->{title} : ($stat->{title} || $id);
        my $category = $song
            ? ($song->{archived}
                ? 'Archived [was ' . $song->{level} . ']'
                : '[' . $song->{level} . '] ' . option_for_level($song->{level})->{name})
            : 'Removed from song list';
        my $average = $stat->{sessions} > 0 ? $stat->{seconds} / $stat->{sessions} : 0;
        printf $out "%-34.34s %-26.26s %12s %8d %8d %7d %12s %-19s %s\n",
            $title, $category, fmt_time($stat->{seconds}), $stat->{sessions},
            $stat->{starts}, ($stat->{manual_edits} // 0), fmt_time($average), $stat->{last}, $id;
    }
}

sub parse_activity_log_row_for_report {
    my ($cols_ref, $practice_options_ref) = @_;

    my @cols = @$cols_ref;
    my $current_practice_count = scalar @$practice_options_ref;
    my $elapsed_start_idx = 2;

    # The log file may contain historical rows written before newer
    # categories were added. For example, rows created before Cold Storage
    # have six target categories, while rows before Jamming have seven.
    #
    # Try the current layout first, then fall back to older, shorter layouts.
    my @candidate_counts = ($current_practice_count);
    for (my $count = $current_practice_count - 1; $count >= 1; $count--) {
        push @candidate_counts, $count;
    }

    for my $candidate_count (@candidate_counts) {
        my $pause_idx                = $elapsed_start_idx + $candidate_count;
        my $pct_start_idx            = $pause_idx + 1;
        my $session_elapsed_idx      = $pct_start_idx + $candidate_count;
        my $active_practice_idx      = $session_elapsed_idx + 1;
        my $practice_session_pct_idx = $active_practice_idx + 1;
        my $current_key_idx          = $practice_session_pct_idx + 1;
        my $state_file_idx           = $current_key_idx + 1;
        my $scales_idx               = $state_file_idx + 1;
        my $ear_training_idx         = $scales_idx + 1;

        next unless defined $cols[$pause_idx]
            && defined $cols[$session_elapsed_idx]
            && defined $cols[$active_practice_idx];

        my $pause_seconds   = parse_hms_time($cols[$pause_idx]);
        my $session_seconds = parse_hms_time($cols[$session_elapsed_idx]);
        my $active_seconds  = parse_hms_time($cols[$active_practice_idx]);

        next unless defined $pause_seconds
            && defined $session_seconds
            && defined $active_seconds;

        my @category_seconds;

        for my $i (0 .. $current_practice_count - 1) {
            my $seconds = 0;

            if ($i < $candidate_count) {
                $seconds = parse_hms_time($cols[$elapsed_start_idx + $i]) // 0;
            }

            push @category_seconds, $seconds;
        }

        my $scales_seconds = parse_hms_time($cols[$scales_idx]) // 0;
        my $ear_training_seconds = parse_hms_time($cols[$ear_training_idx]) // 0;
        my $current_key = $cols[$current_key_idx] // '';

        return {
            category_seconds      => \@category_seconds,
            pause_seconds         => $pause_seconds,
            session_seconds       => $session_seconds,
            active_seconds        => $active_seconds,
            scales_seconds        => $scales_seconds,
            ear_training_seconds  => $ear_training_seconds,
            current_key           => $current_key,
            legacy_category_count => $candidate_count,
            is_legacy_layout      => $candidate_count < $current_practice_count ? 1 : 0,
        };
    }

    return undef;
}

sub write_activity_report {
    my ($tsv_file, $report_file) = @_;

    $tsv_file    //= $LOG_FILE;
    $report_file //= $REPORT_FILE;

    return (0, "No TSV log found to process: $tsv_file")
        unless -e $tsv_file;

    open my $in, '<', $tsv_file
        or return (0, "Could not read $tsv_file: $!");

    # The first TSV row is always comments/header material and is not data.
    my $ignored_first_row = <$in>;

    my @practice_options = practice_options();
    my $practice_count   = scalar @practice_options;

    my $elapsed_start_idx       = 2;
    my $pause_idx               = $elapsed_start_idx + $practice_count;
    my $pct_start_idx           = $pause_idx + 1;
    my $session_elapsed_idx     = $pct_start_idx + $practice_count;
    my $active_practice_idx     = $session_elapsed_idx + 1;
    my $practice_session_pct_idx = $active_practice_idx + 1;
    my $current_key_idx         = $practice_session_pct_idx + 1;
    my $state_file_idx          = $current_key_idx + 1;
    my $scales_idx              = $state_file_idx + 1;

    my %last_row_for_start;
    my @start_order;
    my @dated_snapshot_rows;
    my $raw_data_rows  = 0;
    my $duplicate_rows = 0;
    my $skipped_rows   = 0;
    my $old_rows_excluded = 0;

    while (my $line = <$in>) {
        chomp $line;
        $line =~ s/\r\z//;
        next if $line =~ /^\s*$/;

        $raw_data_rows++;

        my @cols = split /\t/, $line, -1;
        my $session_start_text = $cols[0] // '';

        my ($session_start_epoch, $date_err) = parse_log_stamp($session_start_text);
        if (!defined $session_start_epoch) {
            $skipped_rows++;
            next;
        }
        unless (statistics_include_date($session_start_text)) {
            $old_rows_excluded++;
            next;
        }

        push @dated_snapshot_rows, \@cols;

        # Duplicate rows are matched by the first TSV date/time, which is the
        # session start. The last duplicate row wins.
        if (exists $last_row_for_start{$session_start_text}) {
            $duplicate_rows++;
        }
        else {
            push @start_order, $session_start_text;
        }

        $last_row_for_start{$session_start_text} = \@cols;
    }

    close $in;

    my @rows = map { $last_row_for_start{$_} } @start_order;
    my $daily_snapshots = practice_calendar_totals_from_snapshots(\@dated_snapshot_rows);

    open my $out, '>', $report_file
        or return (0, "Could not write $report_file: $!");

    my $generated_at = fmt_stamp(time);

    print $out "Practice Timer Activity Report\n";
    print $out "==============================\n\n";
    print $out "Generated: $generated_at\n";
    print $out "Source TSV: $tsv_file\n";
    print $out 'Statistics start: ' . ($STATISTICS_START_DATE eq ''
        ? 'all available history' : "$STATISTICS_START_DATE (inclusive)") . "\n";
    print $out "First TSV row ignored as comments/header.\n";
    print $out "Duplicate rule: rows with the same first date/time are duplicates; the last row is used.\n\n";

    # No qualifying timer sessions is still a legitimate reporting window:
    # dated song/category corrections may exist in that period.

    my @category_totals = map { 0 } @practice_options;
    my %active_by_date;
    my $total_session_elapsed = 0;
    my $total_active_practice = 0;
    my $total_pause           = 0;
    my $total_scales          = 0;
    my $total_ear_training    = 0;

    my ($span_start_epoch, $span_start_text);
    my ($span_end_epoch,   $span_end_text);
    if ($STATISTICS_START_DATE ne '') {
        ($span_start_epoch) = parse_log_stamp($STATISTICS_START_DATE . ' 00:00:00');
        $span_start_text = $STATISTICS_START_DATE . ' 00:00:00 (configured statistics start)';
    }

    my @session_lines;
    my $legacy_layout_rows = 0;
    my $format_skipped_rows = 0;

    for my $row (@rows) {
        my @cols = @$row;

        my $session_start_text = $cols[0] // '';
        my $saved_at_text      = $cols[1] // '';

        my ($start_epoch) = parse_log_stamp($session_start_text);
        my ($saved_epoch) = parse_log_stamp($saved_at_text);

        $saved_epoch = $start_epoch if !defined $saved_epoch;
        $saved_at_text = $session_start_text if !defined $saved_at_text || $saved_at_text eq '';

        if (!defined $span_start_epoch || $start_epoch < $span_start_epoch) {
            $span_start_epoch = $start_epoch;
            $span_start_text  = $session_start_text;
        }

        if (!defined $span_end_epoch || $saved_epoch > $span_end_epoch) {
            $span_end_epoch = $saved_epoch;
            $span_end_text  = $saved_at_text;
        }

        my $parsed = parse_activity_log_row_for_report(\@cols, \@practice_options);

        if (!defined $parsed) {
            $format_skipped_rows++;
            next;
        }

        $legacy_layout_rows++ if $parsed->{is_legacy_layout};

        for my $i (0 .. $#practice_options) {
            my $seconds = $parsed->{category_seconds}->[$i] // 0;
            $category_totals[$i] += $seconds;
        }

        my $pause_seconds   = $parsed->{pause_seconds} // 0;
        my $scales_seconds  = $parsed->{scales_seconds} // 0;
        my $ear_training_seconds = $parsed->{ear_training_seconds} // 0;
        my $session_seconds = $parsed->{session_seconds} // 0;
        my $active_seconds  = $parsed->{active_seconds} // 0;

        $total_pause           += $pause_seconds;
        $total_scales          += $scales_seconds;
        $total_ear_training    += $ear_training_seconds;
        $total_session_elapsed += $session_seconds;
        $total_active_practice += $active_seconds;

        my $practice_session_pct = $session_seconds > 0
            ? sprintf('%.1f%%', 100 * $active_seconds / $session_seconds)
            : '0.0%';

        my $current_key = $parsed->{current_key} // '';
        $current_key = 's' if $current_key eq 't';
        my $current_name = '';

        if ($parsed->{is_legacy_layout} && $current_key eq '6') {
            $current_name = 'Pause (legacy key 6)';
        }
        elsif (exists $by_key{$current_key}) {
            $current_name = $by_key{$current_key}->{name};
        }

        push @session_lines, [
            $session_start_text,
            $saved_at_text,
            fmt_time($session_seconds),
            fmt_time($active_seconds + $scales_seconds + $ear_training_seconds),
            fmt_time($active_seconds),
            fmt_time($scales_seconds),
            fmt_time($ear_training_seconds),
            fmt_time($pause_seconds),
            $practice_session_pct,
            $current_key,
            $current_name,
        ];
    }

    %active_by_date = %$daily_snapshots;

    # Apply ONLY explicitly category-synced dated corrections. Song-only
    # corrections affect individual-song stats but not category totals.
    my ($all_dated_entries, $bad_dated_entries) = read_song_adjustment_log($SONG_ADJUST_FILE);
    my @filtered_dated_entries = grep { statistics_include_date($_->{date}) } @$all_dated_entries;
    my $dated_entries = \@filtered_dated_entries;
    my $dated_category_total = 0;
    my $dated_song_only_total = 0;
    for my $entry (@$dated_entries) {
        if (!$entry->{sync}) {
            $dated_song_only_total += $entry->{seconds};
            next;
        }
        for my $i (0 .. $#practice_options) {
            next unless $practice_options[$i]->{key} eq "$entry->{level}";
            $category_totals[$i] += $entry->{seconds};
            last;
        }
        $dated_category_total += $entry->{seconds};
        $active_by_date{$entry->{date}} += $entry->{seconds};
    }
    my $logged_total_active_practice = $total_active_practice;
    $total_active_practice += $dated_category_total;
    my $total_theory_practice = 0;
    for my $i (0 .. $#practice_options) {
        $total_theory_practice += $category_totals[$i]
            if $practice_options[$i]->{key} eq 'y';
    }
    my $total_repertoire_practice = $total_active_practice - $total_theory_practice;

    # Include backdated practice in the report's represented span.
    for my $entry (@$dated_entries) {
        next unless $entry->{seconds} > 0;
        my ($date_epoch) = parse_log_stamp($entry->{date} . ' 00:00:00');
        next unless defined $date_epoch;
        if (!defined($span_start_epoch) || $date_epoch < $span_start_epoch) {
            $span_start_epoch = $date_epoch;
            $span_start_text = $entry->{date} . ' (dated practice)';
        }
    }

    if (!defined $span_end_epoch) {
        $span_end_epoch = time;
        $span_end_text  = fmt_stamp($span_end_epoch) . ' (report generated)';
        if (defined($span_start_epoch) && $span_end_epoch < $span_start_epoch) {
            $span_end_epoch = $span_start_epoch;
            $span_end_text = $STATISTICS_START_DATE . ' 00:00:00 (no practice yet)';
        }
    }

    my $span_seconds = 0;
    $span_seconds = $span_end_epoch - $span_start_epoch
        if defined $span_start_epoch && defined $span_end_epoch;
    $span_seconds = 0 if $span_seconds < 0;

    my $total_reported_active_practice = $total_active_practice + $total_scales + $total_ear_training;

    my $overall_practice_session_pct = $total_session_elapsed > 0
        ? sprintf('%.1f%%', 100 * $logged_total_active_practice / $total_session_elapsed)
        : '0.0%';

    print $out "Span represented\n";
    print $out "----------------\n";
    print $out "Start: $span_start_text\n";
    print $out "End:   $span_end_text\n";
    print $out "Wall-clock span: " . fmt_report_span($span_seconds) . "\n\n";

    print $out "Rows\n";
    print $out "----\n";
    print $out "Raw data rows after ignored first row: $raw_data_rows\n";
    print $out "Older session rows excluded by statistics start: $old_rows_excluded\n";
    print $out "Unique session-start date/times used: " . scalar(@rows) . "\n";
    print $out "Duplicate rows ignored: $duplicate_rows\n";
    print $out "Skipped malformed rows: $skipped_rows\n";
    print $out "Rows with older category layouts handled: $legacy_layout_rows\n";
    print $out "Rows skipped after duplicate filtering because layout was unrecognized: $format_skipped_rows\n\n";

    print $out "Totals\n";
    print $out "------\n";
    print $out "Total session elapsed:        " . fmt_time_decimal($total_session_elapsed) . "\n";
    print $out "Total active practice:        " . fmt_time_decimal($total_reported_active_practice) . "  repertoire + Theory + Scales + Ear training\n";
    print $out "Repertoire practice:          " . fmt_time_decimal($total_repertoire_practice) . "  percentage base\n";
    print $out "Total Theory practice:        " . fmt_time_decimal($total_theory_practice) . "  excluded from repertoire percentages\n";
    print $out "Total Scales practice:        " . fmt_time_decimal($total_scales) . "\n";
    print $out "Total Ear training practice:  " . fmt_time_decimal($total_ear_training) . "\n";
    print $out "Total pause time:             " . fmt_time_decimal($total_pause) . "\n";
    print $out "Practice/session:             $overall_practice_session_pct  timed sessions only\n";
    print $out "Dated song adjustments:       ".scalar(@$dated_entries)." records ($bad_dated_entries invalid)\n";
    print $out "Dated time added to categories: ".fmt_signed_time($dated_category_total)."\n";
    print $out "Dated song-only adjustments:  ".fmt_signed_time($dated_song_only_total)."  affects song stats only\n";
    print $out "Dated category additions are not timer-session elapsed time.\n";
    print $out "Dated practice may fall outside the recorded timer-session span.\n\n";

    # Calendar-day streaks use the report's already-deduplicated practice
    # totals. The reference day is the actual local calendar date, not /n's
    # practice-session date (which may span midnight).
    print_practice_streaks($out, \%active_by_date,
        strftime('%Y-%m-%d', localtime(time)));

    print $out "Category totals\n";
    print $out "---------------\n";
    printf $out "%-34s %12s %10s %12s\n", "Category", "Elapsed", "% Repert.", "Target";
    print $out "-" x 72 . "\n";

    for my $i (0 .. $#practice_options) {
        my $option = $practice_options[$i];
        my $seconds = $category_totals[$i];
        my $pct = $option->{key} eq 'y' ? '-'
            : $total_repertoire_practice > 0
                ? sprintf('%.1f%%', 100 * $seconds / $total_repertoire_practice)
                : '0.0%';

        printf $out "%-34s %12s %10s %12s\n",
            $option->{name},
            fmt_time($seconds),
            $pct,
            target_label($option);
    }

    print $out "\nAdditional tracked totals\n";
    print $out "-------------------------\n";
    print $out "Scales                    " . fmt_time_decimal($total_scales) . "   included in active practice; main-screen target 5-20% of active practice, HIGH after 30 minutes per session\n";
    print $out "Ear training              " . fmt_time_decimal($total_ear_training) . "   included in active practice; main-screen target 5-20% of active practice\n";

    print $out "\nSessions used\n";
    print $out "-------------\n";
    printf $out "%-19s %-19s %12s %12s %12s %12s %12s %12s %10s %s\n",
        "Session start", "Saved at", "Session", "Active", "Target", "Scales", "Ear", "Pause", "Practice", "Current";
    print $out "-" x 152 . "\n";

    for my $line (@session_lines) {
        my ($start, $saved, $session, $active, $target_active, $scales, $ear, $pause, $pct, $key, $name) = @$line;
        my $current = length $key ? "[$key] $name" : '';

        printf $out "%-19s %-19s %12s %12s %12s %12s %12s %12s %10s %s\n",
            $start,
            $saved,
            $session,
            $active,
            $target_active,
            $scales,
            $ear,
            $pause,
            $pct,
            $current;
    }

    my %valid_session_starts = map { ($_->[0] => 1) } @session_lines;
    print_song_stats_for_report($out, $SONG_LOG_FILE, \%valid_session_starts);

    if (@$dated_entries) {
        print $out "\nRecent dated song adjustments (last 20)\n";
        print $out "---------------------------------------\n";
        printf $out "%-19s %-10s %10s %-28s %-8s %s\n",
            'Recorded at', 'Date', 'Change', 'Song', 'Category', 'Note';
        my $start = @$dated_entries > 20 ? @$dated_entries - 20 : 0;
        for my $i ($start .. $#$dated_entries) {
            my $entry = $dated_entries->[$i];
            printf $out "%-19s %-10s %10s %-28.28s %-8s %s\n",
                $entry->{recorded}, $entry->{date}, fmt_signed_time($entry->{seconds}),
                $entry->{title}, ($entry->{sync} ? '['.$entry->{level}.']' : 'song'),
                $entry->{note};
        }
    }

    print_practice_calendar($out, \%active_by_date);
    my $today_ymd = strftime('%Y-%m-%d', localtime(time));
    print_practice_percentiles($out, \%active_by_date, $today_ymd);

    close $out;

    return (
        1,
        "Processed $tsv_file and wrote activity report to $report_file."
    );
}

sub save_all {
    # The active segment is already closed on exit; do not credit stray
    # fractions of a second after the timer has stopped.
    tick_current() if defined $active_segment;

    # Always retain progress for /r, including sessions that are still short.
    # This also lets a short session become loggable after more practice.
    save_state();

    # Do not clutter historical logs with launches, long pauses, or other
    # sessions containing less than one minute of actual practice.
    # Use unrounded seconds; 59.9 seconds does not satisfy the threshold.
    return 0 if reported_active_total() < $MIN_LOGGED_PRACTICE_SECONDS;

    save_log();
    save_song_log();
    return 1;
}

sub cleanup {
    ReadMode('restore');
}

$SIG{INT} = sub {
    $running = 0;
};

# Validate the one editable statistics parameter before entering the UI.
if ($STATISTICS_START_DATE ne '') {
    my ($cutoff_epoch, $cutoff_error) = parse_log_stamp($STATISTICS_START_DATE . ' 00:00:00');
    die "Invalid statistics start date '$STATISTICS_START_DATE': $cutoff_error\n"
        unless defined $cutoff_epoch;
}

my ($START_MODE, $START_TIME_INPUT) = parse_startup_args();

eval {
    initialize_last_practice_clock();
    start_from_command_line($START_MODE, $START_TIME_INPUT);
    $CURRENT_QUOTE = next_quote($QUOTES_FILE);
    start_session_segment();

    # Optional Windows console reader preserves F1-F12.
    # Ordinary character shortcuts (including the number row) still work.
    my $keyboard_warning = initialize();
    $last_message .= ' ' if length($keyboard_warning) && length($last_message);
    $last_message .= $keyboard_warning if length($keyboard_warning);
    ReadMode('cbreak');

    my $last_render = 0;
    my $last_status_render = 0;

    render();
    $last_render = $last_status_render = time;

    while ($running) {
        tick_current();

        my $key = poll_key(sub { ReadKey(-1) });

        if (defined $key) {
            # These aliases apply ONLY at the main timer screen. Prompts
            # keep normal numeric entry for song numbers, menus, and dates.
            # The unshifted number row replaces the former 0-6 direct
            # category selectors at the user's request.
            my %number_row = (
                '1' => 'p',  '2' => 'f',  '3' => 'F3', '4' => 'v',
                '5' => 'g',  '6' => 'r',  '7' => 's',  '8' => 'h',
                '9' => 'y',  '0' => 'm',
            );
            $key = $number_row{$key} if exists $number_row{$key};
            $key = { F1 => 'p', F2 => 'f', F4 => 'v', F5 => 'g' }->{$key} // $key;
            my $raw_key = $key;
            my $key_lc  = lc $key;
            # Any submenu can print over or reposition the console. Force a
            # clean main-screen frame on return, never on periodic refresh.
            invalidate_main_screen() if $raw_key =~ /^(?:F8|F9|F10|F3|T|P)$/
                || $key_lc =~ /^(?:u|r|f|a|c|d|v|l|n|m|t|e|s|h|y|z)$/;


            if ($raw_key eq 'S') {
                my $logged = save_all();
                $last_message = $logged
                    ? "Saved session to $STATE_FILE and appended $LOG_FILE."
                    : "Saved session for /r; history not logged (under 1 minute of actual practice).";
                render();
                $last_render = $last_status_render = time;
            }
            elsif ($key_lc eq 'u') {
                # Finish the current interval so it can be undone reliably.
                # Confirmation time does not get credited to the timer.
                finish_session_segment();
                undo_latest_practice();
                $last_tick = time;
                start_session_segment();
                render();
                $last_render = $last_status_render = time;
            }
            elsif ($key_lc eq 'g') {
                # Tip selection lives in its own experimental module.
                # It does not interrupt practice timing or change categories.
                my ($song, $error) = PracticeTips::next_tip(
                    $SONG_CATEGORY_FILE, $LOG_FILE, $SONG_LOG_FILE,
                    $SONG_ADJUST_FILE, $session_start_stamp, \%song_elapsed,
                    today_qualified_song_seconds(),
                );
                # A successful refresh needs no extra status line; the new
                # one-line tip itself is shown immediately above the quote.
                $last_message = $error // '';
                render();
                $last_render = $last_status_render = time;
            }
            elsif ($key_lc eq 'r') {
                # A tip's launch key chooses the song printed on the LAST
                # screen, not a possibly newer recommendation recalculated
                # after the key was pressed. Match Find's timeline boundary.
                if (!length $displayed_tip_song_id) {
                    $last_message = 'No recommended song to practice (a reminder may be due).';
                }
                else {
                    finish_session_segment();
                    practice_displayed_tip_song($displayed_tip_song_id);
                    start_session_segment();
                }
                render();
                $last_render = $last_status_render = time;
            }
            elsif ($raw_key eq 'F8') {
                # Direct shortcut to the full Song Attributes submenu,
                # without first visiting Song Categories (c -> t).
                finish_session_segment();
                $last_message = show_attributes_hotkey();
                start_session_segment();
                render();
                $last_render = $last_status_render = time;
            }
            elsif ($raw_key eq 'F10') {
                # Direct shortcut to the existing Emphasize attribute report.
                # No selection/category change, and menu time is excluded.
                finish_session_segment();
                $last_message = show_emphasize_report_hotkey();
                start_session_segment();
                render();
                $last_render = $last_status_render = time;
            }
            elsif ($key_lc eq 'l') {
                # Generate and open the gVim activity report directly, without
                # entering View or changing the current practice selection.
                finish_session_segment();
                $last_message = open_updated_activity_report_in_gvim();
                $last_tick = time; # Report generation/launching isn't practice.
                start_session_segment();
                render();
                $last_render = $last_status_render = time;
            }
            elsif ($raw_key eq 'F3') {
                # Open media for the active or paused song/activity without
                # starting another selection, and without counting menu time.
                finish_session_segment();
                my ($id, $title) = current_material_owner();
                $last_message = defined($id)
                    ? open_all_attached_media($id)
                    : 'Select a song, Scales, Ear training, or Theory before opening media.';
                $last_tick = time;
                start_session_segment();
                render();
                $last_render = $last_status_render = time;
            }
            elsif ($key_lc eq 'b' || $raw_key eq 'F6' || $raw_key eq 'F7') {
                # Bump existing category totals without touching the active
                # song/timer/selection. F7 is the same as the old b(n) key.
                my $bump_key = $raw_key eq 'F6' ? 'y' : 's';
                $last_message = bump_practice_minute($bump_key);
                render();
                $last_render = $last_status_render = time;
            }
            elsif ($raw_key eq 'T' || $raw_key eq 'P' || $key_lc eq 'f'
                || $key_lc eq 'a' || $key_lc eq 'c'
                || $key_lc eq 'd' || $key_lc eq 'v' || $key_lc eq 'n'
                || $key_lc eq 'm' || $raw_key eq 't' || $raw_key eq 'F9'
                || $key_lc eq 'e' || $key_lc eq 'z') {
                finish_session_segment();
                if ($raw_key eq 'T') {
                    prompt_session_start();
                }
                elsif ($raw_key eq 'P' || $key_lc eq 'f') {
                    prompt_song_search();
                }
                elsif ($key_lc eq 'a') {
                    prompt_adjustment();
                }
                elsif ($key_lc eq 'c') {
                    show_song_categories();
                }
                elsif ($key_lc eq 'n') {
                    $last_message = prompt_add_new_song();
                }
                elsif ($raw_key eq 't' || $raw_key eq 'F9') {
                    prompt_current_song_media();
                }
                elsif ($key_lc eq 'e') {
                    prompt_edit_current_mp3();
                }
                elsif ($key_lc eq 'd') {
                    show_descriptions();
                }
                elsif ($key_lc eq 'z') {
                    show_repertoire_guide();
                }
                elsif ($key_lc eq 'm') {
                    manage_custom_tips();
                }
                else {
                    show_current_session_details();
                }
                start_session_segment();
                render();
                $last_render = $last_status_render = time;
            }
            elsif (exists $by_key{$key_lc} && !$by_key{$key_lc}->{is_adjust}
                && !$by_key{$key_lc}->{is_retired}) {
                finish_session_segment();
                if ($key_lc eq pause_key()) {
                    toggle_pause_selection();
                }
                else {
                    # A deliberate new category overrides any suspended work.
                    clear_resume_selection();
                    $current_key = $key_lc;
                    $undo_locked = 0;
                    clear_current_song();
                    $last_message = '';
                    my ($media_id) = media_category_owner($current_key);
                    if (defined $media_id) {
                        # Scales, Ear training, and Theory use the shared
                        # None / All / Some media prompt.
                        # They are activities, not repertoire song selections.
                        ReadMode('restore');
                        $last_message = offer_song_media_on_selection($media_id);
                        ReadMode('cbreak');
                        $last_tick = time; # Media question time isn't practice.
                    }
                }
                start_session_segment();
                render();
                $last_render = $last_status_render = time;
            }
            elsif ($key_lc eq 'q' || $key_lc eq 'x') {
                $running = 0;
            }
        }

        # Category timers/rankings stay on ten-second refreshes; in between,
        # update the status and selected-song timers once per second.
        if (time - $last_render >= $UPDATE_INTERVAL) {
            render();
            $last_render = $last_status_render = time;
        }
        elsif (time - $last_status_render >= $STATUS_LINE_UPDATE_INTERVAL) {
            refresh_main_status_line();
            $last_status_render = time;
        }

        sleep 0.10;
    }

    finish_session_segment();
    persist_last_practice_epoch(1);
    my $logged = save_all();
    $last_message = $logged ? 'Session added to historical logs.'
        : 'Session saved for /r, but not added to historical logs (under 1 minute of actual practice).';

    my ($report_ok, $report_msg) = write_activity_report($LOG_FILE, $REPORT_FILE);
    $activity_report_message = $report_msg;
};

my $err = $@;
cleanup();

die $err if $err;

clear_screen();

print "Saved reloadable session to $STATE_FILE\n";
if (reported_active_total() >= $MIN_LOGGED_PRACTICE_SECONDS) {
    print "Appended human-readable log to $LOG_FILE\n";
    print "Updated per-song history in $SONG_LOG_FILE\n" if keys %song_elapsed;
}
else {
    print "Session under 1 minute of actual practice; historical logs not updated.\n";
}
print "Dated song adjustments: $SONG_ADJUST_FILE\n" if -e $SONG_ADJUST_FILE;
print "$activity_report_message\n" if length $activity_report_message;
print "\n";

if (grep { ($_ // 0) > 0.001 } values %song_elapsed) {
    my $song_time = 0;
    $song_time += $_ for values %song_elapsed;
    my $song_count = scalar(grep { ($_ // 0) > 0.001 } values %song_elapsed);
    print "Song-specific practice this session: " . fmt_time_decimal($song_time) . " across $song_count song(s)\n\n";
}

print "Final totals:\n";
print "-------------\n";
print "Session started:  " . $session_start_stamp . "\n";
print "Session elapsed:  " . fmt_time_decimal(session_elapsed()) . "\n";
print "Active practice:  " . fmt_time_decimal(reported_active_total()) . "  including Theory, Scales and Ear training\n";
print "Repertoire:       " . fmt_time_decimal(repertoire_total()) . "  percentage base\n";
print "Theory practice:  " . fmt_time_decimal(theory_total()) . "  excluded from repertoire percentages\n";
my $final_theory_today = theory_seconds_today();
print "Theory today:     " . fmt_time_decimal($final_theory_today) . "  "
    . theory_daily_status($final_theory_today) . " (target 10-20 minutes/day)\n";

my $final_scales_key = scales_key();
if (defined $final_scales_key) {
    print "Scales practice:  " . fmt_time_decimal($elapsed{$final_scales_key}) . "\n";
}

my $final_ear_key = ear_training_key();
if (defined $final_ear_key) {
    print "Ear training:     " . fmt_time_decimal($elapsed{$final_ear_key}) . "\n";
}

print "Practice/session: " . practice_session_percent_whole() . "%  repertoire + Theory (excluding Scales/Ear training)\n\n";

for my $option (practice_options()) {
    next if $option->{key} eq 'y'; # Shown separately above.
    printf "%-34s %25s  %3d%%  target %s\n",
        $option->{name} . ":",
        fmt_time_decimal($elapsed{ $option->{key} }),
        percent_whole($option->{key}),
        target_label($option);
}

my $scales_key = scales_key();

if (defined $scales_key) {
    printf "%-34s %25s  %s\n",
        "Scales:",
        fmt_time_decimal($elapsed{$scales_key}),
        supplemental_status_for($by_key{$scales_key}) . " (" .
            int(supplemental_percent_for($scales_key) + 0.5) . "% of active; max 30m)";
}

my $ear_key = ear_training_key();
if (defined $ear_key) {
    printf "%-34s %25s  %s\n",
        "Ear training:",
        fmt_time_decimal($elapsed{$ear_key}),
        supplemental_status_for($by_key{$ear_key}) . " (" .
            int(supplemental_percent_for($ear_key) + 0.5) . "% of active)";
}

my $pause_key = pause_key();

printf "%-34s %25s\n",
    "Pause:",
    fmt_time_decimal($elapsed{$pause_key});

print "\nGood practice.\n";



