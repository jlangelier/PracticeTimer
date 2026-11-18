package PracticeAudit;
use strict;
use warnings;
use POSIX qw(strftime);
use Fcntl qw(:flock);
use Time::Local qw(timegm);
use Exporter 'import';
our @EXPORT_OK = qw(append_events timestamp);

# One event per TSV line; no header because the first field of EVERY line is
# an ISO 8601 local timestamp with numeric UTC offset.
# Fields: timestamp, action, permanent_id, previous_value, new_value, detail.
sub timestamp {
    my ($epoch) = @_;
    $epoch = time() unless defined $epoch;
    my @parts = localtime($epoch);
    my $date = strftime('%Y-%m-%dT%H:%M:%S', @parts);
    my $tz = strftime('%z', @parts);
    unless (defined $tz && $tz =~ /^[+-]\d{4}$/) {
        # Fallback for Perl C runtime versions without %z support.
        my $offset = timegm(@parts[0..5]) - $epoch;
        $tz = sprintf('%s%02d%02d', $offset < 0 ? '-' : '+',
            int(abs($offset) / 3600), int((abs($offset) % 3600) / 60));
    }
    return "$date" . substr($tz, 0, 3) . ':' . substr($tz, 3, 2);
}

sub _safe {
    my ($value) = @_;
    $value = '' unless defined $value;
    $value =~ s/[\t\r\n]+/ /g;
    return $value;
}

sub append_events {
    my ($file, $events) = @_;
    return (1, '') unless $events && @$events;
    open my $fh, '>>', $file or return (0, "Cannot open audit log '$file': $!");
    unless (flock($fh, LOCK_EX)) {
        my $err = $!;
        close $fh;
        return (0, "Cannot lock audit log '$file': $err");
    }
    my $stamp = timestamp();
    my $data = join('', map {
        join("\t", $stamp, map { _safe($_) }
            @{$_}{qw(action id old new detail)}) . "\n"
    } @$events);
    my $printed = print {$fh} $data;
    my $closed = close $fh;
    return (!$printed || !$closed)
        ? (0, "Failed to append event to audit log '$file': $!")
        : (1, '');
}
1;
