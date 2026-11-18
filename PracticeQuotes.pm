package PracticeQuotes;
use strict;
use warnings;
use Exporter 'import';
our @EXPORT_OK = qw(next_quote);

# Each nonempty, non-comment line in quotes.txt is a quote.
# A single comment line records the last displayed index.
sub next_quote {
    my ($file) = @_;
    my @quotes;
    my $last = -1;
    if (open my $in, '<', $file) {
        while (my $line = <$in>) {
            $line =~ s/\r?\n\z//;
            if ($line =~ /^#\s*last_shown_index\s*=\s*(\-?\d+)\s*$/i) {
                $last = $1;
            } elsif ($line !~ /^\s*#/ && $line =~ /\S/) {
                push @quotes, $line;
            }
        }
        close $in;
    } elsif (-e $file) {
        warn "Cannot read quotes file $file: $!\n";
        return '';
    }
    return '' unless @quotes;
    my $index = ($last + 1) % @quotes;
    my $tmp = "$file.tmp.$$";
    if (open my $out, '>', $tmp) {
        print {$out} "$_\n" for @quotes;
        print {$out} "# last_shown_index=$index\n";
        if (!close $out || !rename($tmp, $file)) {
            warn "Could not update quote rotation in $file: $!\n";
            unlink $tmp;
        }
    } else {
        warn "Could not write quote rotation to $file: $!\n";
    }
    return $quotes[$index];
}
1;
