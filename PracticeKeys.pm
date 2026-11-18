package PracticeKeys;
use strict;
use warnings;
use Exporter 'import';
use Time::HiRes qw(time);

our @EXPORT_OK = qw(initialize poll_key key_from_console_event);

# Term::ReadKey on Windows exposes the ASCII character of a console key
# event; F1-F12 have ASCII value zero. Win32::Console retains the virtual
# key code, so use its input-event reader when present. The timer's normal
# Term::ReadKey input remains a fallback, including on other platforms.
my $console;
my $console_down = {};
my $pending_escape = '';
my $escape_started = 0;

my %ansi_function_keys = (
    "\eOP"   => 'F1', "\eOQ"   => 'F2',
    "\eOR"   => 'F3', "\eOS"   => 'F4',
    "\e[11~" => 'F1', "\e[12~" => 'F2',
    "\e[13~" => 'F3', "\e[14~" => 'F4',
    "\e[15~" => 'F5',
    "\e[17~" => 'F6', "\e[18~" => 'F7',
    "\e[19~" => 'F8',
    "\e[20~" => 'F9', "\e[21~" => 'F10',
    "\e[23~" => 'F11', "\e[24~" => 'F12',
);

sub initialize {
    $console = undef;
    $console_down = {};
    $pending_escape = '';
    $escape_started = 0;
    return '' unless $^O eq 'MSWin32';

    my $ok = eval {
        require Win32::Console;
        Win32::Console->import(qw(STD_INPUT_HANDLE));
        my $input_handle = Win32::Console::STD_INPUT_HANDLE();
        $console = Win32::Console->new($input_handle);
        die 'could not open Windows console input' unless defined $console;
        my $count = $console->GetEvents();
        die 'could not inspect Windows console input' unless defined $count;
        1;
    };
    if (!$ok) {
        $console = undef;
        return 'Function keys unavailable: install Win32::Console (cpanm Win32::Console). Character shortcuts still work.';
    }
    return '';
}

# Win32::Console::Input returns: event type, keydown, repeat count,
# virtual key code, scan code, ASCII code, modifier flags.
sub key_from_console_event {
    my ($down, @event) = @_;
    return undef unless @event >= 7;
    my ($event_type, $key_down, $repeat_count, $vk, $scan, $ascii, $modifiers) = @event;
    return undef unless defined($event_type) && $event_type == 1;
    return undef unless defined($vk) && $vk =~ /^\d+$/;
    if ($vk >= 112 && $vk <= 123) { # F1-F12
        if (!$key_down) {
            delete $down->{$vk};
            return undef;
        }
        # Holding F1 must not repeatedly pause/unpause.
        return undef if $down->{$vk};
        $down->{$vk} = 1;
        return 'F' . ($vk - 111);
    }
    return undef unless $key_down;
    return undef unless defined $ascii;
    if ($ascii =~ /^\d+$/) {
        return undef if $ascii == 0 || $ascii > 255;
        return chr($ascii);
    }
    return length($ascii) == 1 && ord($ascii) ? $ascii : undef;
}

sub _raw_byte {
    my ($read_character) = @_;
    if (defined $console) {
        # Do not block; Windows delivers both key-down and key-up events.
        # Consume stale key-up/shift events without delaying the next tick.
        for (1 .. 40) {
            my $count = $console->GetEvents();
            unless (defined $count) {
                $console = undef;
                return $read_character->();
            }
            return undef if $count == 0;
            my @event = $console->Input();
            my $key = key_from_console_event($console_down, @event);
            return $key if defined $key;
        }
        return undef;
    }
    return $read_character->();
}

sub poll_key {
    my ($read_character) = @_;
    # On Win32 with Win32::Console, named function keys come back directly.
    # Escape sequences are also handled for non-Windows terminals, and for
    # console hosts that send VT-style input instead of Windows key events.
    for (1 .. 10) {
        my $key = _raw_byte($read_character);
        if (!defined $key) {
            if (length($pending_escape) && time - $escape_started > 0.8) {
                $pending_escape = '';
            }
            return undef;
        }
        return $key if $key =~ /^F(?:[1-9]|1[0-2])$/;
        if (!length $pending_escape) {
            if ($key eq "\e") {
                $pending_escape = $key;
                $escape_started = time;
                next;
            }
            return $key;
        }
        $pending_escape .= $key;
        if (exists $ansi_function_keys{$pending_escape}) {
            my $mapped = $ansi_function_keys{$pending_escape};
            $pending_escape = '';
            return $mapped;
        }
        if (!grep { index($_, $pending_escape) == 0 } keys %ansi_function_keys) {
            $pending_escape = '';
        }
    }
    return undef;
}

1;
