package PracticeTips;

use strict;
use warnings;
use POSIX qw(strftime);
use File::Basename qw(dirname);
use File::Spec;
use Time::Local qw(timelocal);

# Experimental, self-contained one-line tip generator for practice_timer.pl.
# The main program calls show_tip() once when rendering its closing text.
# Comment out that single call to disable tips.
#
# A song with at least 60 credited seconds in the current /n practice day
# is no longer eligible until the next new practice day. This applies to manual g choices too.
my $DAILY_SUGGESTION_RETIRE_SECONDS = 60;

# Only levels 1-4 are suggested by default: the working repertoire.
# Levels 0 (Keystones), 5 (Back Burner) and 6 (Cold Storage) are deliberately
# excluded because those categories do not call for routine attention.
# Change these keys later if the experiment should consider more categories.
my %SUGGEST_LEVEL = map { $_ => 1 } (1, 2, 3, 4);

# A manually requested tip cycles through the ten least-practiced songs.
# Keep this bounded so repeated presses still suggest neglected material.
my $ROTATION_POOL_SIZE = 10;

# Disk data is cached across the timer's frequent screen redraws.
# A change to any source file invalidates the cache automatically.
my $CACHE_SIGNATURE;
my $CACHE_DATA;

# Display the tip and return the recommended song's permanent ID (if any).
# The caller can use this ID to launch the SAME song currently displayed,
# without guessing from its title or repeating the search.
sub show_tip {
    my ($tip, $song_id) = _tip_with_song(@_);
    if (defined $tip && length $tip) {
        my $shortcut = defined($song_id) && length($song_id)
            ? '  [r(o) Practice this song]' : '';
        print "\nTip: $tip$shortcut\n";
    }
    return $song_id;
}

# Preserve the original text-only interface for existing callers/tests.
sub tip_for {
    my ($tip) = _tip_with_song(@_);
    return $tip;
}

# The text and ID are obtained in one selection, so a status redraw and a
# direct-launch hotkey never disagree about the song being suggested.
sub _tip_with_song {
    my ($catalog_file, $activity_file, $song_log_file, $adjust_file,
        $current_session, $live_song_seconds, $today_live_song_seconds) = @_;
    my $practice_day = _practice_day($current_session);

    # Due reminders are text only; the hotkey must never attempt to launch
    # a song merely because a reminder happens to mention its title.
    my ($reminder) = _oldest_due_custom_tip($catalog_file);
    return ('[Reminder] ' . $reminder->{text}, undef) if $reminder;

    my @songs = _eligible_songs_for_today(
        $catalog_file, $activity_file, $song_log_file, $adjust_file,
        $current_session, $live_song_seconds, $today_live_song_seconds,
    );
    return (undef, undef) unless @{ _cached_disk_data(
        $catalog_file, $activity_file, $song_log_file, $adjust_file, $practice_day,
    )->{catalog} };
    return ('All eligible songs have received at least a minute of practice today.', undef)
        unless @songs;

    my $selected = _selected_song($catalog_file, \@songs, $practice_day);
    return (_tip_text($selected), $selected->{id});
}

# Called only when the user presses g. Select a *different* song and remember
# it for the remainder of the /n practice day, including across restarts.
# Returns (title, error); an error is nonfatal and may be shown on screen.
sub next_tip {
    my ($catalog_file, $activity_file, $song_log_file, $adjust_file,
        $current_session, $live_song_seconds, $today_live_song_seconds) = @_;
    my $practice_day = _practice_day($current_session);

    # Pressing g must not hide an outstanding scheduled reminder.
    my ($reminder) = _oldest_due_custom_tip($catalog_file);
    return (undef, 'A reminder is due. Press m to delete it when done.')
        if $reminder;

    my @songs = _eligible_songs_for_today(
        $catalog_file, $activity_file, $song_log_file, $adjust_file,
        $current_session, $live_song_seconds, $today_live_song_seconds,
    );
    return (undef, 'No eligible songs for practice tips.')
        unless @{ _cached_disk_data(
            $catalog_file, $activity_file, $song_log_file, $adjust_file, $practice_day,
        )->{catalog} };
    return (undef, 'No unpracticed eligible songs remain for today.') unless @songs;

    my @pool = @songs[0 .. ((@songs < $ROTATION_POOL_SIZE
        ? scalar(@songs) : $ROTATION_POOL_SIZE) - 1)];
    return (undef, 'Only one eligible song; no alternative tip available.')
        if @pool == 1;

    my $current = _selected_song($catalog_file, \@songs, $practice_day);
    my $index = -1;
    for my $i (0 .. $#pool) {
        if ($pool[$i]{id} eq $current->{id}) {
            $index = $i;
            last;
        }
    }
    # A previous manual selection can leave the lowest-ten pool after more
    # practice is recorded. In that case, start with the lowest-ranked song.
    my $next = $pool[($index + 1) % @pool];
    my $error = _save_choice($catalog_file, $practice_day, $next->{id});
    return ($next->{title}, $error);
}


# ---------------------------------------------------------------------------
# Scheduled custom tips: deliberately independent of timer/session state.
# File: practice_custom_tips.tsv in the same folder as the song catalog.
# Records are append-only additions, reschedules, and deletions. A deletion
# removes a reminder without rewriting previous data, even on Windows.
# A <tab> id <tab> created_epoch <tab> due_epoch <tab> hex(text)
# R <tab> id <tab> changed_epoch <tab> new_due_epoch
# D <tab> id
# Keeping this private to PracticeTips.pm makes the feature easy to disable.
# ---------------------------------------------------------------------------

sub _custom_tip_file {
    my ($catalog_file) = @_;
    return File::Spec->catfile(dirname($catalog_file // '.'),
        'practice_custom_tips.tsv');
}

sub _read_custom_tips {
    my ($catalog_file) = @_;
    my $path = _custom_tip_file($catalog_file);
    return ([], 0, undef) if !-e $path;
    open my $fh, '<', $path
        or return (undef, undef, "Could not open $path: $!");

    my (%items, $last_id);
    $last_id = 0;
    while (my $row = <$fh>) {
        chomp $row;
        $row =~ s/\r\z//;
        next if $row =~ /^\s*(?:#|\z)/;
        my @parts = split /\t/, $row, -1;
        if ($parts[0] eq 'A' && @parts == 5) {
            my ($type, $id, $created, $due, $encoded) = @parts;
            next unless $id =~ /\A[1-9]\d*\z/
                && $created =~ /\A\d+\z/ && $due =~ /\A\d+\z/
                && $encoded =~ /\A(?:[0-9a-f]{2})+\z/;
            $last_id = $id if $id > $last_id;
            my $content = pack('H*', $encoded);
            $items{$id} = {
                id => 0 + $id,
                created => 0 + $created,
                due => 0 + $due,
                text => $content,
            };
        }
        elsif ($parts[0] eq 'R' && @parts == 4
                && $parts[1] =~ /\A[1-9]\d*\z/
                && $parts[2] =~ /\A\d+\z/
                && $parts[3] =~ /\A[1-9]\d*\z/) {
            # Only update a reminder that is still present. Preserve its
            # original ID, creation time, and text; all previous R records
            # remain in the append-only history.
            my ($type, $id, $changed_at, $new_due) = @parts;
            $items{$id}{due} = 0 + $new_due if exists $items{$id};
        }
        elsif ($parts[0] eq 'D' && @parts == 2
                && $parts[1] =~ /\A[1-9]\d*\z/) {
            my $id = $parts[1];
            $last_id = $id if $id > $last_id;
            delete $items{$id};
        }
    }
    close $fh or return (undef, undef, "Could not finish reading $path: $!");
    my @sorted = sort {
        $a->{due} <=> $b->{due}
            || $a->{created} <=> $b->{created}
            || $a->{id} <=> $b->{id}
    } values %items;
    return (\@sorted, $last_id, undef);
}

# Returns (active reminders sorted by due date, error).
sub list_custom_tips {
    my ($catalog_file) = @_;
    my ($items, $last_id, $error) = _read_custom_tips($catalog_file);
    return ($items, $error);
}

sub _oldest_due_custom_tip {
    my ($catalog_file, $now) = @_;
    $now = time unless defined $now;
    my ($items, $last_id, $error) = _read_custom_tips($catalog_file);
    return (undef, $error) if $error;
    for my $item (@$items) {
        return ($item, undef) if $item->{due} <= $now;
        last; # Already sorted by due time; all remaining are in the future.
    }
    return (undef, undef);
}

# Delay examples: 1d5h, 3d, 7h, 15m, 2h30m.
# Also accepts local absolute time: YYYY-MM-DD HH:MM.
sub parse_custom_tip_time {
    my ($spec, $now) = @_;
    $spec //= '';
    $spec =~ s/^\s+|\s+\z//g;
    $now = time unless defined $now;
    my $compact = lc $spec;
    $compact =~ s/\s+//g;
    if ($compact =~ /\A(?:(\d+)d)?(?:(\d+)h)?(?:(\d+)m)?\z/
        && length($compact)) {
        my ($days, $hours, $minutes) = ($1 // 0, $2 // 0, $3 // 0);
        my $seconds = $days * 86400 + $hours * 3600 + $minutes * 60;
        return (undef, 'Duration must be greater than zero.') unless $seconds > 0;
        return (undef, 'Duration is too large (maximum ten years).')
            if $seconds > 3653 * 86400;
        return (int($now + $seconds), undef);
    }
    if ($spec =~ /\A(\d{4})-(\d\d)-(\d\d)\s+(\d\d):(\d\d)(?::(\d\d))?\z/) {
        my ($year, $month, $day, $hour, $minute, $second) =
            ($1, $2, $3, $4, $5, $6 // 0);
        my $due;
        eval { $due = timelocal($second, $minute, $hour, $day, $month - 1, $year); };
        return (undef, 'Invalid calendar date/time.') if $@;
        my $wanted = sprintf('%04d-%02d-%02d %02d:%02d:%02d',
            $year, $month, $day, $hour, $minute, $second);
        return (undef, 'Invalid calendar date/time.')
            unless strftime('%Y-%m-%d %H:%M:%S', localtime($due)) eq $wanted;
        return (undef, 'The reminder must be in the future.') if $due <= $now;
        return ($due, undef);
    }
    return (undef, 'Use a delay like 1d5h, 2h, 30m, or YYYY-MM-DD HH:MM.');
}

# Returns (saved entry, error), never modifies live practice timing.
sub add_custom_tip {
    my ($catalog_file, $message, $when, $now) = @_;
    $now = time unless defined $now;
    $message //= '';
    $message =~ s/[\r\n\t]+/ /g;
    $message =~ s/^\s+|\s+\z//g;
    return (undef, 'Reminder text cannot be empty.') unless length $message;
    return (undef, 'Reminder is too long (maximum 500 characters).')
        if length($message) > 500;

    my ($due, $error) = parse_custom_tip_time($when, $now);
    return (undef, $error) if $error;
    my ($items, $max_id, $load_error) = _read_custom_tips($catalog_file);
    return (undef, $load_error) if $load_error;
    my $id = $max_id + 1;
    my $path = _custom_tip_file($catalog_file);
    open my $fh, '>>', $path
        or return (undef, "Could not save reminder to $path: $!");
    print {$fh} join("\t", 'A', $id, int($now), $due, unpack('H*', $message)) . "\n"
        or do { close $fh; return (undef, "Could not write reminder to $path: $!"); };
    close $fh or return (undef, "Could not finish saving reminder to $path: $!");
    return ({id => $id, created => int($now), due => $due, text => $message}, undef);
}

# Parse a signed relative time shift: +2d1h, -3h, +30m, or 2d (add).
# Does not accept an absolute time. Returns (signed seconds, error).
sub parse_custom_tip_shift {
    my ($spec) = @_;
    $spec //= '';
    $spec = lc $spec;
    $spec =~ s/\s+//g;
    my $sign = $spec =~ s/\A-// ? -1 : 1;
    $spec =~ s/\A\+// if $sign > 0;
    if (length($spec) &&
        $spec =~ /\A(?:(\d+)d)?(?:(\d+)h)?(?:(\d+)m)?\z/) {
        my ($days, $hours, $minutes) = ($1 // 0, $2 // 0, $3 // 0);
        my $seconds = $days * 86400 + $hours * 3600 + $minutes * 60;
        return (undef, 'Time adjustment must be greater than zero.')
            unless $seconds > 0;
        return (undef, 'Time adjustment is too large (maximum ten years).')
            if $seconds > 3653 * 86400;
        return ($sign * $seconds, undef);
    }
    return (undef, 'Use +2d1h, -3h, +30m, or 2d (adds time).');
}

# Append a reschedule record rather than rewriting the reminder file.
# For an overdue reminder, a positive adjustment starts from NOW so adding
# time always places the reminder back in the pending queue. Otherwise, the
# adjustment is relative to the original scheduled due time. Negative shifts
# always move the stored due time earlier.
# Returns (updated reminder, error).
sub adjust_custom_tip_time {
    my ($catalog_file, $id, $spec, $now) = @_;
    $now = time unless defined $now;
    my ($delta, $parse_error) = parse_custom_tip_shift($spec);
    return (undef, $parse_error) if $parse_error;

    my ($items, $max_id, $read_error) = _read_custom_tips($catalog_file);
    return (undef, $read_error) if $read_error;
    my ($item) = grep { $_->{id} eq ($id // '') } @$items;
    return (undef, 'That reminder does not exist.') unless $item;

    my $base = $delta > 0 && $item->{due} <= $now
        ? int($now) : $item->{due};
    my $new_due = int($base + $delta);
    return (undef, 'Adjustment would move the reminder before 1970.')
        if $new_due <= 0;

    my $path = _custom_tip_file($catalog_file);
    open my $fh, '>>', $path
        or return (undef, "Could not update $path: $!");
    print {$fh} join("\t", 'R', $id, int($now), $new_due) . "\n"
        or do { close $fh; return (undef, "Could not reschedule reminder in $path: $!"); };
    close $fh or return (undef, "Could not finish rescheduling reminder in $path: $!");
    return ({ %$item, due => $new_due }, undef);
}

# Returns (success, error). Deleted reminders never override song tips again.
sub delete_custom_tip {
    my ($catalog_file, $id) = @_;
    my ($items, $max_id, $error) = _read_custom_tips($catalog_file);
    return (0, $error) if $error;
    my ($selected) = grep { $_->{id} eq ($id // '') } @$items;
    return (0, 'That reminder does not exist.') unless $selected;
    my $path = _custom_tip_file($catalog_file);
    open my $fh, '>>', $path
        or return (0, "Could not update $path: $!");
    print {$fh} "D\t$id\n"
        or do { close $fh; return (0, "Could not delete reminder in $path: $!"); };
    close $fh or return (0, "Could not finish deleting reminder in $path: $!");
    return (1, undef);
}

# Used by BOTH the automatic tip and the g hotkey. Recomputing this at
# every redraw is intentional: completing a qualifying song selection makes
# the song ineligible immediately, even if g had pinned it earlier today.
# Custom reminders are handled before this step and are not filtered.
sub _eligible_songs_for_today {
    my ($catalog_file, $activity_file, $song_log_file, $adjust_file,
        $current_session, $live_song_seconds, $today_live_song_seconds) = @_;

    my $practice_day = _practice_day($current_session);
    my @ranked = _ranked_songs(
        $catalog_file, $activity_file, $song_log_file, $adjust_file,
        $current_session, $live_song_seconds,
    );
    my $data = _cached_disk_data(
        $catalog_file, $activity_file, $song_log_file, $adjust_file, $practice_day,
    );

    # Historical sessions assigned to this /n practice day plus dated
    # adjustments for that date. Do not split the same session at midnight.
    my %today = %{ $data->{daily_seconds} };

    # Replace this session's disk snapshot with its live, qualified
    # segments, rather than adding the same practice twice. All qualified
    # segments in the current session belong to its /n practice day.
    my $session = $current_session // '';
    if (ref($today_live_song_seconds) eq 'HASH') {
        for my $key (keys %{ $data->{session_daily_seconds} }) {
            my ($start, $id) = split /\0/, $key, 2;
            next unless $start eq $session;
            $today{$id} -= $data->{session_daily_seconds}{$key};
        }
        for my $id (keys %$today_live_song_seconds) {
            $today{$id} += $today_live_song_seconds->{$id};
        }
    }

    return grep { ($today{$_->{id}} // 0) + 0.001 <
        $DAILY_SUGGESTION_RETIRE_SECONDS } @ranked;
}

sub _ranked_songs {
    my ($catalog_file, $activity_file, $song_log_file, $adjust_file,
        $current_session, $live_song_seconds) = @_;

    $live_song_seconds ||= {};
    my $data = _cached_disk_data(
        $catalog_file, $activity_file, $song_log_file, $adjust_file,
        _practice_day($current_session),
    );

    # The current session may already be in the saved snapshot log. Replace
    # its on-disk cumulative values with live ones; NEVER add both.
    my %totals = %{ $data->{historical_seconds} };
    for my $song_id (keys %$live_song_seconds) {
        my $on_disk = $data->{session_seconds}{
            ($current_session // '') . "\0" . $song_id
        } // 0;
        my $live = $live_song_seconds->{$song_id} // 0;
        $totals{$song_id} += $live - $on_disk;
    }

    my @ranked = map {
        +{ %$_, seconds => (($totals{$_->{id}} // 0) > 0
            ? ($totals{$_->{id}} // 0) : 0) }
    } @{ $data->{catalog} };

    # Least-practiced first; deterministic ties avoid redraw flicker.
    return sort {
        $a->{seconds} <=> $b->{seconds}
            || lc($a->{title}) cmp lc($b->{title})
            || $a->{id} cmp $b->{id}
    } @ranked;
}

sub _selected_song {
    my ($catalog_file, $songs, $practice_day) = @_;
    $practice_day = _practice_day() unless defined $practice_day;
    my ($stored_day, $stored_id) = _read_choice($catalog_file);
    my $today = $practice_day;

    # A manual selection is valid only on the day it was requested.
    if (defined($stored_day) && $stored_day eq $today) {
        for my $song (@$songs) {
            return $song if $song->{id} eq $stored_id;
        }
    }

    # Original behavior: rotate daily among songs tied for the very lowest
    # practice time. No state file is needed for automatic tips.
    my $min = $songs->[0]{seconds};
    my @least = grep { abs($_->{seconds} - $min) <= 0.01 } @$songs;
    my ($year, $month, $day) = split /-/, $practice_day;
    my $epoch = timelocal(0, 0, 12, $day, $month - 1, $year);
    my $day_number = 0 + strftime('%Y%j', localtime($epoch));
    return $least[$day_number % @least];
}

sub _tip_text {
    my ($song) = @_;
    my $seconds = $song->{seconds};
    return qq{Give "$song->{title}" a try; no practice recorded yet.}
        if $seconds < 0.5;
    return qq{Consider "$song->{title}"; only } . _duration($seconds)
        . ' of practice recorded.';
}

sub _today {
    return strftime('%Y-%m-%d', localtime);
}

# The timer's /n session start, not midnight, defines its practice day.
# Older callers without a session stamp retain local-calendar fallback.
sub _practice_day {
    my ($session_start) = @_;
    return substr($session_start, 0, 10)
        if defined($session_start)
        && $session_start =~ /^\d{4}-\d{2}-\d{2}[ T]\d{2}:\d{2}:\d{2}$/;
    return _today();
}

# The state file belongs entirely to this experimental module. Its location
# follows the song catalog, so the program needs no extra state variables.
sub _choice_file {
    my ($catalog_file) = @_;
    return File::Spec->catfile(dirname($catalog_file), 'practice_tip_choice.state');
}

sub _read_choice {
    my ($catalog_file) = @_;
    my $file = _choice_file($catalog_file);
    return unless open my $fh, '<', $file;
    my $line = <$fh> // '';
    close $fh;
    chomp $line;
    my ($date, $hex) = split /\t/, $line, 2;
    return unless defined($date) && $date =~ /^\d{4}-\d\d-\d\d$/;
    return unless defined($hex) && $hex =~ /^(?:[0-9a-f]{2})+$/;
    return ($date, pack('H*', $hex));
}

sub _save_choice {
    my ($catalog_file, $day, $song_id) = @_;
    my $file = _choice_file($catalog_file);
    open my $fh, '>', $file
        or return "Could not save tip selection to $file: $!";
    print {$fh} "$day\t" . unpack('H*', $song_id) . "\n";
    close $fh or return "Could not finish saving tip selection to $file: $!";
    return;
}

sub _duration {
    my ($seconds) = @_;
    return 'less than 1 minute' if $seconds < 60;
    my $minutes = int($seconds / 60 + 0.5);
    return "$minutes minute" . ($minutes == 1 ? '' : 's') if $minutes < 60;
    my $hours = int($minutes / 60);
    my $remainder = $minutes % 60;
    return "$hours hour" . ($hours == 1 ? '' : 's')
        . ($remainder ? " $remainder minutes" : '');
}

sub _cached_disk_data {
    my (@arguments) = @_;
    my @files = @arguments[0 .. 3];
    my $practice_day = $arguments[4] // _today();
    # Changing /n changes the practice day; midnight alone does not.
    my $signature = $practice_day . "\x1c" . join "\x1f", map {
        my $file = defined $_ ? $_ : '';
        my @st = stat($file);
        join "\x1e", $file, (@st ? ($st[9], $st[7]) : ('missing', ''));
    } @files;

    if (!defined($CACHE_SIGNATURE) || $signature ne $CACHE_SIGNATURE) {
        my ($catalog_file, $activity_file, $song_log_file, $adjust_file) = @files;
        my $catalog = _read_catalog($catalog_file);
        my $valid_sessions = _read_sessions($activity_file);
        my ($history, $session_seconds, $session_daily) =
            _read_song_snapshots($song_log_file, $valid_sessions, $practice_day);
        my %daily;
        for my $key (keys %$session_daily) {
            my (undef, $id) = split /\0/, $key, 2;
            $daily{$id} += $session_daily->{$key};
        }
        _apply_dated_adjustments($adjust_file, $history, \%daily, $practice_day);
        $CACHE_DATA = {
            catalog => $catalog,
            historical_seconds => $history,
            session_seconds => $session_seconds,
            daily_seconds => \%daily,
            session_daily_seconds => $session_daily,
        };
        $CACHE_SIGNATURE = $signature;
    }
    return $CACHE_DATA;
}

sub _read_catalog {
    my ($file) = @_;
    my @songs;
    return \@songs unless defined $file && open my $fh, '<', $file;

    my %seen_ids;
    while (my $line = <$fh>) {
        chomp $line;
        $line =~ s/\r\z//;
        next if $line =~ /^\s*\z/;
        my ($level, $number, $title, $id, $status) = split /\t/, $line, 5;
        # Keep archived songs' historical logs intact but never recommend them.
        $status //= '';
        $status =~ s/^\s+|\s+$//g;
        next if lc($status) eq 'archived';
        next unless defined($level) && $SUGGEST_LEVEL{$level // ''};
        next unless defined($number) && $number =~ /^\d+\z/;
        next unless defined($title) && $title =~ /\S/;
        $title =~ s/^\s+|\s+$//g;
        $id //= '';
        $id =~ s/^\s+|\s+$//g;

        # Older three-column lists get provisional IDs matching the script's
        # slugging convention. This module never changes the song list.
        if ($id eq '' || $seen_ids{$id}) {
            my $base = lc($title);
            $base =~ s/[^a-z0-9]+/_/g;
            $base =~ s/^_+|_+$//g;
            $base = 'song' unless length $base;
            $id = $base;
            my $suffix = 2;
            $id = $base . '_' . $suffix++ while $seen_ids{$id};
        }
        $seen_ids{$id} = 1;
        push @songs, { id => $id, title => $title };
    }
    close $fh;
    return \@songs;
}

sub _read_sessions {
    my ($file) = @_;
    my %valid;
    return \%valid unless defined $file && open my $fh, '<', $file;
    my $header = <$fh>;
    while (my $line = <$fh>) {
        my ($start) = split /\t/, $line;
        $valid{$start} = 1
            if defined($start) && $start =~ /^\d{4}-\d\d-\d\d \d\d:\d\d:\d\d\z/;
    }
    close $fh;
    return \%valid;
}

sub _read_song_snapshots {
    my ($file, $valid_sessions, $practice_day) = @_;
    my (%latest, %totals, %daily);
    return (\%totals, \%latest, \%daily)
        unless defined $file && open my $fh, '<', $file;
    my $header = <$fh>;
    while (my $line = <$fh>) {
        chomp $line;
        $line =~ s/\r\z//;
        my ($session, $saved, $id, $title, $seconds, $starts, $last) =
            split /\t/, $line, -1;
        next unless defined($session) && exists $valid_sessions->{$session};
        next unless defined($id) && length($id);
        next unless defined($seconds)
            && $seconds =~ /\A(?:\d+(?:\.\d*)?|\.\d+)\z/;
        my $key = $session . "\0" . $id;
        # Snapshots accumulate per session/song. The FINAL one wins.
        $latest{$key} = 0 + $seconds;
    }
    close $fh;
    for my $key (keys %latest) {
        my ($session, $id) = split /\0/, $key, 2;
        $totals{$id} += $latest{$key};
        # The entire session is credited to its /n start date, even if
        # some of its playing or its final save happened after midnight.
        $daily{$key} = $latest{$key}
            if substr($session, 0, 10) eq $practice_day;
    }
    return (\%totals, \%latest, \%daily);
}

sub _apply_dated_adjustments {
    my ($file, $totals, $today_seconds, $today) = @_;
    return unless defined $file && open my $fh, '<', $file;
    my $header = <$fh>;
    while (my $line = <$fh>) {
        chomp $line;
        $line =~ s/\r\z//;
        my ($recorded, $date, $id, $title, $level, $delta, $sync) =
            split /\t/, $line, -1;
        next unless defined($id) && length($id);
        next unless defined($date) && $date =~ /^\d{4}-\d\d-\d\d\z/;
        next unless defined($level) && $level =~ /^[0-6]\z/;
        next unless defined($sync) && $sync =~ /^[01]\z/;
        next unless defined($delta)
            && $delta =~ /\A[+-]?(?:\d+(?:\.\d*)?|\.\d+)\z/;
        $totals->{$id} += 0 + $delta;
        $today_seconds->{$id} += 0 + $delta if $date eq $today;
    }
    close $fh;
}

1;
