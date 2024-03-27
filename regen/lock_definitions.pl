#!/usr/bin/perl -w
#23456789112345678921234567893123456789412345678951234567896123456789712345678981
use Data::Dumper;
$Data::Dumper::Sortkeys = 1;

# Regenerate (overwriting only if changed):

#    lock_definitions.h

# Also accepts the standard regen_lib -q and -v args.

# This script is normally invoked from regen.pl.

BEGIN {
    require './regen/regen_lib.pl';
}

use strict;
use warnings;

my $me = 'regen/lock_definitions.pl';
my $MAX_LINE_WIDTH = 78;
my $comment_columns = $MAX_LINE_WIDTH - 3;  # For "/* " on first line; " * "
                                            # on subsequent ones
my %conditionals;   # Accumulated list of functions that require restrictions
                    # on their input parameters to be thread-safe.
my %functions;      # Accumulated data for each function in the input
my %has_comments;   # Accumulated list of functions with comments at their
                    # entries
my %need_single_thread_init;    # Accumulated list of functions that need
                                # single-thread initialization
my %non_functions;  # Accumulated list of non-function inputs
my %non_posixes;    # Accumulated list of functions not in POSIX
my %obsoletes;      # Accumulated list of obsolete functions
my %preferred;      # Accumulated list of functions which have preferred
                    # alternatives
my %race_tags;      # Accumulated tags for the input 'race:tag' elements
my %signal_issues;  # Accumulated list of functions that are affected by signals
my %unsuitables;    # Accumulated list of entirely thread-unsafe functions
my $preprocessor = "";   # Preprocessor conditional in effect
my %categories = ( LC_ALL => 1 );

sub open_print_header {
    my ($file, $quote) = @_;
    return open_new($file, '>',
                    { by => $me,
                      from => "data in $me",
                      file => $file, style => '*',
                      copyright => [2023..2024],
                      quote => $quote });
}

my $reentr_pl = "./regen/reentr.pl";
open my $auto, "<", $reentr_pl or die "Can't open $reentr_pl: $!";
while (<$auto>) {
    last if /^__DATA__/;
}

my %automatics;
while (<$auto>) {
    my ($function, @rest) = split /\s*\|\s*/, $_;
    $function =~ s/ \s .* //x;
    my $reentrant = "${function}_r";
    $automatics{$function} = $reentrant;
}
close $auto or die "Can't close $reentr_pl: $!";

my $l = open_print_header('lock_definitions.h');
print $l <<EOF;
EOF

sub name_order {    # sort helper
       lc $a =~ s/[\W_]*//gr cmp lc $b =~ s/[\W_]*//gr
    or lc $a cmp lc $b;
}

my @DATA = <DATA>;
close DATA;

while (defined (my $line = shift @DATA)) {

    my (@cfunctions, @cdata);
    {
        do {
            chomp $line;
            $line =~ s/ \s+ $ //x;
            my $continued = $line =~ s/ \s* \\ $ //x;
            #print STDERR __FILE__, ": ", __LINE__, ": $continued: $line\n"; 
            if ($line =~ / ^ ( [^|]* ) \s* \| \s* (.*) /x) {
                push @cfunctions, $1;
                push @cdata, $2;
            }
            elsif ($line =~ / ^ \S /x) {
                push @cfunctions, $line;
            }
            else {
            #print STDERR __FILE__, ": ", __LINE__, ": $continued: $line\n"; 
                push @cdata, $line =~ s/ ^ \s+ //rx;
            }

            last unless $continued;

            $line = shift @DATA;
        } while (1);
    }

            #print STDERR __FILE__, ": ", __LINE__, ": $line\n"; 
    $line = join " ", @cfunctions;
            #print STDERR __FILE__, ": ", __LINE__, ": $line\n", Dumper \@cdata; 
    $line .= "|" . join " ", @cdata if @cdata ;#&& (@cdata > 1 || $cdata[0] ne "");
            #print STDERR __FILE__, ": ", __LINE__, ": $line\n"; 

    my ($functions, $data, $dummy) = split /\s*\|\s*/, $line;
    croak("Extra '|' in input '$_'") if defined $dummy;

    # This line has a continuation if the functions list ends in a comma.  All
    # continuations have just the one field.
    if ($data) {
        while ($functions =~ / , \s* $/x) {
            my $continuation = shift @DATA;
            chomp $continuation;
            $functions .= $continuation;
        }

        $line = "$functions|$data";
    }

    next if $line =~ /^\s*$/;       # Empty
    next if $line =~ m|^\s*//|;     # Begins with a // comment
    last if $line =~ /^__END__/;    

    #print STDERR __FILE__, ": ", __LINE__, ": $line\n";

    if ($line =~ / ^ \# (.*) /x) {
        $preprocessor = "$1";
        $preprocessor = "" if $preprocessor =~ /^endif/;
        next;
    }

    croak "line with only one column: '$line'" unless defined $data;

    # Fields in the data column
    my @categories;
    my @races;
    my @conditions;
    my @signals;
    my $has_comment = 0;
    my @notes;
    my %locks;
    my $unsuitable;
    my $non_function = 0;
    my $non_posix = 0;
    my $obsolete;
    my $preferred;
    my $timer = 0;
    my $need_init = 0;

    # Loop through the data column, processing and removing one
    # field each iteration
    while ($data =~ /\S/) {
        $data =~ s/^\s+//;
        $data =~ s/\s+$//;
            
        if ($data =~ s| // \s* ( .* ) $ ||x) {
            push @notes, "$1";
            $has_comment = 1;
            next;
        }

        if ($data =~ s/ ^ U \b //x) {
            $unsuitable = "";
            next;
        }

        if ($data =~ s/ ^ X \b //x) {
            push @notes, "has never been in the POSIX Standard, or was removed"
                       . " as of POSIX 2001";
            $non_posix = 1;
            next;
        }

        if ($data =~ s/ ^ [MV] \b //x) {
            $non_function = 1;
            next;
        }

        if ($data =~ s! ^ race
                                  # An optional tag in $1 marked by an initial
                                  # colon
                                  (?: : ( \w+ )

                                    # which may be followed by an optional
                                    # condition in $2 marked by an initial
                                    # slash
                                    (?: / ( \S+ ) )?
                                  )?
                                \b
                               !!x)
        {
            my $race = $1 // "";
            my $condition = $2 // "";
            if ($condition) {
                push @conditions, $condition;
            }
            else {
                push @races, $race;
            }
            next;
        }

        if ($data =~ s/ ^ ( LC_\S+ ) //x) {
            push @categories, $1;
            $categories{$1} = 1;
            next;
        }

        if ($data =~ s/ ^ sig: ( \S+ ) //x) {
            push @signals, $1;
            next;
        }

        if ($data =~ s/ ^ ( init ) \b //x) {
            push @notes, "must be called at least once in single-threaded mode"
                       . " to enable thread-safety in subsequent calls when in"
                       . " multi-threaded mode.";

            $need_init = 1;
            next;
        }

        if ($data =~ s/ ^ ( timer ) \b //x) {
            $timer = 1;
            next;
        }

        if ($data =~ s/ ^ const: ( \S+ ) //x) {
            croak("lock type redefined:" . $line)
                                             if $locks{$1} && $locks{$1} ne 'x';
            $locks{$1} = 'x';
            next;
        }

        if ($data =~ s/ ^ ( [[:lower:]]+ ) //x) {
            croak("lock type redefined:" . $line)
                                             if $locks{$1} && $locks{$1} ne 'r';
            $locks{$1} = 'r';
            next;
        }

        if ($data =~ s/ ^ O " ( [^"]+  ) " //x) {
            $obsolete = $1;
            unshift @notes, "Obsolete; $obsolete";
            next;
        }

        # The preferred functions (if any) follow the 'O'
        if ($data =~ s/ ^ ( O | PF? ) ( [,\w]* ) //x) {
            my $type = $1;

            if ($type eq 'PF') {
                $preferred = "a Perl $2-family macro";
                unshift @notes, "Use $preferred instead";
                next;
            }

            my @list = map { "$_()" } split ",", $2;
            my $list = "";
            if (@list) {
                $list[-1] = "or $list[-1]" if @list > 1;
                $list = join ", ", @list;
                $list =~ s/,// if @list == 2;
            }

            if ($type eq 'O') {
                $obsolete = $list;
                unshift @notes, "Obsolete";
                $notes[0] .= "; use $list instead" if $obsolete;
            }
            elsif ($type eq 'P') {
                $preferred = $list;
                unshift @notes, "Use $list instead";
            }

            next;
        }

        croak("Unexpected input '$data'") if $data =~ /\S/;
    }

    # Now have assembled all the data for the functions

    # The Linux man pages include this keyword with no explanation.  khw
    # thinks it is obsolete because it always seems associated with SIGALRM.
    # But add this check to be sure.
    croak ("'timer' keyword not associated with signal ALRM")
                                if $timer && ! grep { $_ eq 'ALRM' } @signals;

    push @categories, "LC_ALL" if defined $locks{locale} && @categories == 0;

    # Apply the data to each function.
    foreach my $function (split /\s*,\s*/, $functions) {
        croak("Illegal function syntax: '$function'") if $function =~ /\W/;
        if (grep { $_->{preprocessor} eq  $preprocessor }
                                            $functions{$function}{entries}->@*)
        {
            croak("$function already has an entry")
        }

        my %entry;
        $entry{preprocessor} = $preprocessor;
        push $entry{categories}->@*, @categories if @categories;
        push $entry{races}->@*, @races if @races;
        if (@conditions) {
            push $entry{conditions}->@*, @conditions;
            $conditionals{$function} = 1;
        }
        if (@signals) {
            push $entry{signals}->@*, @signals;
            $signal_issues{$function} = 1;
        }
        $entry{locks}{$_} = $locks{$_} for keys %locks;
        $need_single_thread_init{$function} = 1 if $need_init;
        push $entry{notes}->@*, @notes if @notes;
        if (defined $unsuitable) {
            $entry{unsuitable} = 1;
            $unsuitables{$function} = 1;
        }

        if (defined $obsolete) {
            $obsoletes{$function} = $obsolete;
        }

        if (defined $preferred) {
            $preferred{$function} = $preferred;
        }

        if ($non_function) {
            $entry{non_function} = 1;
            $non_functions{$function} = 1;
        }

        if ($non_posix) {
            $non_posixes{$function} = 1;
        }

        $has_comments{$function} = 1 if $has_comment || $non_posix;
            
        if (@races > 1 || (@races && $races[0] ne "")) {
            $race_tags{$_}{$function} = 1 for @races;
        }

        push $functions{$function}{entries}->@*, \%entry;
    }
}

sub output_list_with_heading {
    my ($list_ref, $heading) = @_;

    return unless $list_ref->@*;

    print $l $heading if $heading;

    my @sorted = sort name_order $list_ref->@*;
    my $list = columnarize_list(\@sorted, $comment_columns);
    $list =~ s/^/ * /gm;
    print $l $list;
}

output_list_with_heading([ keys %functions ], <<EOT
/* This file contains macros to wrap their respective libc accesses to ensure
 * that those accesses are thread-safe in a multi-threaded environment.
 *
 * Accesses are mostly function calls but there are a few macros and variables
 * as well.  Most libc accesses are already thread-safe without these
 * wrappers, so do not appear here.  The accesses that are known to have
 * multi-thread issues are:
 *
EOT
);

output_list_with_heading([ keys %non_functions ], <<EOT
 *
 * If an access doesn't appear in the above list, perl thinks it is
 * thread-safe on all platforms.  If your experience is otherwise, add an
 * entry in the DATA portion of $me.
 *
 * If you use any of the above listed items, this file is for you.
 *
 * All the accesses listed above are function calls, except for these:
 *
EOT
);

print $l <<EOT;
 *
 * A few functions are considered obsolete, and should not be used, at least
 * in new code.  Along with any preferred alternatives, these are:
 *
EOT

sub output_columnarized_hash {
    my ($handle, $hash_ref) = @_;

    my $max_width = 0;

    foreach my $function (keys $hash_ref->%*) {
        my $width = length $function;
        $max_width = $width if $width > $max_width
    }
    $max_width += 2;    # To allow for trailing "()"

    foreach my $function (sort name_order keys $hash_ref->%*) {
        printf $handle " * %-${max_width}s  %s\n",
                       "$function()", $hash_ref->{$function};
    }
}

output_columnarized_hash($l, \%obsoletes);

foreach my $function (keys %unsuitables) {
    my $prefix = (defined $preferred{$function}) ? '@' : " "; 
    $unsuitables{"$prefix$function"} = delete $unsuitables{$function};
}

output_list_with_heading([ keys %unsuitables ], <<EOT
 *
 * More detailed information may be available at the #define entry for the
 * respective lock below.
 *
 * A few functions are considered totally unsuited for use in a multi-thread
 * environment.  These must be called only during single-thread operation,
 * hence no UNLOCK wrapper macro is generated for these, and the generated
 * LOCK macro is designed to give a compilation error.
 *
EOT
);

output_list_with_heading([ keys %need_single_thread_init, ], <<EOT
 *
 * There are preferred alternatives on some platforms for the functions marked
 * with '\@' above, and which may be suitable for multi-thread use.  See below
 * for the list of preferred alternatives.
 *
 * Some functions perform initialization on their first call that must be done
 * while still in a single-thread environment, but subsequent calls are
 * thread-safe when wrapped with the respective macros defined in this file.
 * Therefore, they must be called at least once before switching to
 * multi-threads:
 *
EOT
);

print $l <<EOT;
 *
 * Some libc functions use and/or modify a global state, such as a database.
 * The libc functions presume that there is only one thread at a time
 * operating on that database.  Unpredictable results occur if more than one
 * does, even if the database is not changed.  For example, typically there is
 * a global iterator for such a data base and that iterator is maintained by
 * libc, so that each new read from any thread advances it, meaning that no
 * thread will see all the entries.  The only way to make these thread-safe is
 * to have an exclusive lock on a mutex from the open call through the close.
 * This is beyond the current scope of this header.  You are advised to not
 * use such databases from more than one thread at a time.  The locking macros
 * here only are designed to make the individual function calls thread-safe
 * just for the duration of the call.  Comments at each definition tell what
 * other functions have races with that function.  Typically the functions
 * that fall into this class have races with other functions whose names begin
 * with "end", such as "endgrent()".
 *
 * Other examples of functions that use a global state include pseudo-random
 * number generators.  Some libc implementations of 'rand()', for example, may
 * share the data across threads; and others may have per-thread data.  The
 * shared ones will have unreproducible results, as the threads vary in their
 * timings and interactions.  This may be what you want; or it may not be.
 * (This particular function is a candidate to be removed from the POSIX
 * Standard because of these issues.)
 *
 * When one thread does a chdir(2), it affects the whole process, and any libc
 * call that is expecting a stable working directory will be adversely
 * affected.  The man pages only list one such call, nftw().  But there may
 * be other issues lurking.
 *
 * Functions that output to a stream also are considered thread-unsafe when
 * locking is not done.  But the typical consequences are just that the data
 * is output in unpredictable ways, which may be totally acceptable.  However,
 * it is beyond the scope of these macros to make sure that formatted output
 * uses a non-dot radix decimal point.  Use the
 * WITH_LC_NUMERIC_SET_TO_NEEDED() macro documented in perlapi to accomplish
 * this.
 *
 * The rest of the functions, when wrapped with their respective LOCK and
 * UNLOCK macros, should be thread-safe.
EOT
output_list_with_heading([ keys %conditionals ], <<EOT
 *
 * However, some of these are not thread-safe if called with arguments that
 * don't comply with certain (easily-met) restrictions.  These are:
 *
EOT
);

output_list_with_heading([ keys %signal_issues ], <<EOT
 *
 * The details on each restriction are documented below where their respective
 * locking macros are #defined.  The macros assume that the function is called
 * with the appropriate restrictions.
 *
 * The macros here do not help in coping with asynchronous signals.  For
 * these, you need to see the vendor man pages.  The functions here known to
 * be vulnerable to signals are:
 *
EOT
);

print $l <<EOT;
 *
 * Some libc's implement 'system()' thread-safely.  But in others, it also
 * has signal issues.
 *
 * There are better ways of accomplishing the same action for many of the
 * functions.  This can be for various reasons, but the most common ones are
 * either 1) there is an equivalent reentrant function with fewer (perhaps no)
 * races; and/or 2) the function involves locales, and Perl doesn't expose the
 * current underlying locale except within the scope of a "use locale"
 * statement.  Using the perl-furnished macros and functions hides all that
 * from you.
 *
 * Below is a list all such functions and their preferred alternatives.  Many
 * of these can be automatically selected for you.  That is, if you use a
 * function that has a preferred alternative, your code actually is compiled
 * to transparently use the preferred alternative instead.  This feature is
 * enabled by default for code in the Perl core and its extensions.  To enable
 * it in other XS modules,
 *
 *    #define PERL_REENTRANT
 *
 * In the list below, the functions you always have to manually substitute the
 * preferred version for are marked with an '\@'.  Unmarked ones get their
 * preferred alternative automatically substituted for them when this feature
 * is enabled.  For these, it is better to use the unpreferred version, and
 * rely on this feature to do the right thing, in part because no substitution
 * is done if the alternative is not available on the platform nor if threads
 * aren't enabled.  You just write as if there weren't threads, and you get
 * the better behavior without having to think about it.  You still should
 * wrap your function calls with the locking macros #defined in this file.
 * These also are automatically changed by this feature to use the macros for
 * the selected alternative, which just might end up expanding to be a no-op.
 *
 * Even so, some of the preferred alternatives are considered obsolete or
 * otherwise unwise to use.  These are marked with a '?', and you need to look
 * elsewhere in this file for details.  Also, some alternatives aren't in the
 * POSIX Standard or aren't Perl-defined functions, so won't be widely
 * available.  These are marked with '~'.  (Remember that the automatic
 * substitution only happens when they are available, so you can just use the
 * unpreferred alternative.)
 *
 * If something you are using is on the list of problematic functions below,
 * you should examine the comments where the locking macros for it are
 * #defined.
 *
EOT

my %curated_preferred;
#print STDERR __FILE__, ": ", __LINE__, ": ", Dumper \%functions;#, \%race_tags;

foreach my $bad (keys %automatics) {
    my $better = $automatics{$bad};
    if (! defined $functions{$better}) {
        #print STDERR __FILE__, ": ", __LINE__, ": '$better'\n"; 
    }

    my $prefix = " ";
    if (defined $obsoletes{$bad}) {
        #print STDERR __FILE__, ": ", __LINE__, ": ", $better, "\n";
        $prefix = "?";
    }
    elsif (defined $non_posixes{$better}) {
        $prefix = "~";
    }
    elsif (defined $preferred{$bad}) {
        if ($preferred{$bad} =~ s/\(\)//r eq $better) {
            $prefix = " ";
            delete $preferred{$bad};
        }
        else {
            #print STDERR __FILE__, ": ", __LINE__, ": ", $preferred{$bad}, "\n";
        }
    }
    else {
        $prefix = "~";
    }
    $curated_preferred{" $bad"} = "$prefix$better()";
}
#print STDERR __FILE__, ": ", __LINE__, ": ", Dumper \%non_posixes;

foreach my $bad (keys %preferred) {
    my $better = $preferred{$bad};
    my $prefix = (defined $non_posixes{$better}) ? '~' : " ";
#    print STDERR __FILE__, ": ", __LINE__, ": $bad: $better";
#    print STDERR " $non_posixes{$better}" if $non_posixes{$better};
#    print STDERR "\n";
    $curated_preferred{"\@$bad"} = "$prefix$better";
}

#print STDERR __FILE__, ": ", __LINE__, ": ", Dumper \%automatics;

output_columnarized_hash($l, \%curated_preferred);

output_list_with_heading([ keys %has_comments ], <<EOT
 *
 * And there are other functions that are problematic in some way other than
 * those already given.  Please refer to their respective lock definitions
 * below for any caveats (or more information) for functions in this list: 
 *
EOT
);

print $l <<EOT;
 *
 * In addition, the locale-related functions introduced in POSIX 2008 are not
 * portable to platforms that don't support them; for example any Windows one.
 * Perl has extensive code to hide the differences from your code.  You should
 * be using Perl_setlocale() to change and query the locale; and don't use
 * functions like uselocale(), or any function that takes a locale_t parameter
 * (typically such functions have the suffix "_l" in their names).  Keep in
 * mind that the current locale is assumed to be "C" for all Perl programs
 * except within the scope of "use locale", or when calling certain functions
 * in the POSIX module.  The perl core sorts all of this out for you; most
 * functions that deal directly with locale information should not be used.
 *
 * In theory, you should wrap every instance of every function listed here
 * with its corresponding LOCK/UNLOCK macros, except as noted above.  The
 * macros here all should expand to no-ops when run from an unthreaded perl.
 * Many also expand to no-ops on various other platforms and Configurations.
 * They exist so you you don't have to worry about this.  Some definitions are
 * no-ops in all current cases, but you should wrap their functions anyway, as
 * future work likely will yield Configurations where they aren't just no-ops.
 *
 * You may override any definitions here simply by #defining your own before
 * #including this file (which likely means before #including perl.h).
 *
 * Best practice is to call the LOCK macro; call the function and copy the
 * result to a per-thread place if that result points to a buffer internal to
 * libc; then UNLOCK it immediately.  After that, you can act on the result.
 *
 * The macros here are generated from an internal DATA section in
 * $me, populated from information derived from the
 * POSIX 2017 Standard and Linux glibc section 3 man pages (supplemented by
 * other vendor's man pages).  (Linux tends to have extra restrictions not in
 * the Standard, and its man pages are typically more detailed than the
 * Standard and other vendors, who may also have the same restrictions, but
 * just don't document them.) The data can easily be adjusted as necessary.
 *
 * The macros generated here expand to other macro calls that are expected to
 * be #defined in perl.h, depending on the platform and Configuration.  Many
 * of the thread vulnerabilities involve the program's environment and locale,
 * so perl has separate mutexes for each of those two types of access.  There
 * are a few others, all rare or obsolete.   There are also many races, where
 * certain functions concurrently executing in different threads can interfere
 * with each other unpredictably.  This header file currently lumps all races
 * and non-environment/locale vulnerabilities into a third, generic, mutex.
 * So the macro names are various combinations of the three mutexes, and
 * whether the lock needs to be exclusive (suffix "x" in the lock name) or
 * non-exclusive (suffix "r" for read-only).  GEN means the generic mutex; ENV
 * the environment one; and LC the locale one.
 *
 * The lumping into the single generic mutex is due to the expectation that
 * such calls are infrequent enough that having a single mutex for all won't
 * noticeably affect performance, and that the more mutexes you have, the more
 * likely deadlock can occur.  Individual cases could be separated into
 * separate mutexes if necessary.  perl.h takes further steps in the expansion
 * of these macros to avoid deadlock altogether.
 */
EOT

# Beware that the Standard contains weasel words that could make multi-thread
# safety a fiction, depending on the application.  Our experience though is
# that libc implementations don't take advantage of this loophole, and the
# macros here are written as if it didn't exist.  (See
# https://stackoverflow.com/questions/78056645 )  The actual text is:
#
#    A thread-safe function can be safely invoked concurrently with other
#    calls to the same function, or with calls to any other thread-safe
#    functions, by multiple threads. Each function defined in the System
#    Interfaces volume of POSIX.1-2017 is thread-safe unless explicitly stated
#    otherwise. Examples are any 'pure' function, a function which holds a
#    mutex locked while it is accessing static storage or objects shared
#    among threads.
#
# Note that this doesn't say anything about the behavior of a thread-safe
# function when executing concurrently with a thread-unsafe function.  This
# effectively gives permission for a libc implementation to make every
# allegedly thread-safe function not be thread-safe for circumstances outside
# the control of the thread.  This would wreak havoc on a lot of code if libc
# implementations took much advantage of this loophole.  But it is a reason
# to avoid creating many mutexes.  If all threads lock on the same mutex when
# executing a thread-unsafe function, they defeat the weasel words.
#
# Another reason to minimize the number of mutexes is that each additional one
# increases the possibility of deadlock, unless the code is carefully
# crafted (and remains so during future maintenance).
#

#print STDERR __FILE__, ": ", __LINE__, ": ", Dumper \%functions;#, \%race_tags;

# The locale macros take a mask parameter with each affected category having a
# bit set in it.  The mask for LC_ALL is the same across all platforms.
print $l <<~EOT;

/* The macros that include locale locking need to know (in some
 * Configurations) which locale categories are affected.  This is done by
 * passing a bit mask argument to them, with each affected category having a
 * corresponding bit set.  The definitions below convert from category to its
 * bit position. */
#define LC_ALLb_  LC_INDEX_TO_BIT_(LC_ALL_INDEX_)
EOT

print $l <<~EOT;

/*  On platforms where the locale for a given category must be matched by the
 *  LC_CTYPE locale to avoid potential mojibake, set things up to also
 *  automatically include the LC_CTYPE bit. */
#if defined(LC_CTYPE) && defined(PERL_MUST_DEAL_WITH_MISMATCHED_CTYPE)
#  define INCLUDE_CTYPE_  LC_INDEX_TO_BIT_(LC_CTYPE_INDEX_)
#else
#  define INCLUDE_CTYPE_  0
#endif

/* Then #define the bit position for each category on the system that can play
 * a part in the locking macro definitions */
EOT

# Create the mask for each category found in the DATA
foreach my $cat (sort keys %categories) {
    next if $cat eq "LC_ALL";
    print $l <<~EOT;
      #ifdef $cat
      #  define ${cat}b_  LC_INDEX_TO_BIT_(${cat}_INDEX_)|INCLUDE_CTYPE_
      #else
      #  define ${cat}b_  LC_ALLb_
      #endif
      EOT
}

print $l <<~EOT;

/* Then finally the locking macros */
EOT

# Output the computed results for each function in the DATA
foreach my $function (sort name_order keys %functions) {

    #print STDERR __FILE__, ": ", __LINE__, ": ", Dumper $function, $functions{$function}->{entries};

    my $FUNC = uc $function;
    print $l "\n#ifndef ${FUNC}_LOCK\n";

    # If this function has at least one version that depends on a preprocessor
    # directive, and there isn't an #else one, automatically add one which
    # will expand to no-ops.
    if (   $functions{$function}{entries}[0]{preprocessor} ne ""
        && $functions{$function}{entries}[-1]{preprocessor} ne 'else')
    {
        push $functions{$function}->{entries}->@*, { preprocessor => 'else' };
    }

    # For each possibility for this function ...
    foreach my $entry ($functions{$function}->{entries}->@*) {
        my @comments;
        #print STDERR __FILE__, ": ", __LINE__, ": ", Dumper $function, $entry;

        my $indent = "  ";      # We are within the scope of the above #ifndef
        my $dindent = $indent;  # Indentation for #define lines
        if ($entry->{preprocessor}) {
            print $l "#$indent$entry->{preprocessor}\n";
            $dindent .= "  ";   # #define indentation increased as a result
        }

        my $columns = $comment_columns - length $dindent;
        my $output_function_name = $function;

        # Non-functions don't get "()"
        $output_function_name .= "()" unless $entry->{non_function};

        $output_function_name .= " ";

        my $hanging = " " x length $output_function_name;   # indentation

        # First accumulate all the comments for this entry
        if ($entry->{notes}) {
            foreach my $note ($entry->{notes}->@*) {
                push @comments, split "\n", wrap($columns, "", $hanging,
                                                $output_function_name . $note);
            }
        }

        if ($entry->{signals}) {
            my $signal_count = $entry->{signals}->@*;
            my $text = "${output_function_name}is vulnerable to signal";
            $text .= "s" if $signal_count > 1;
            $text .= " " . join(", ", $entry->{signals}->@*);
            push @comments, split "\n", wrap($columns, "", $hanging, $text);
        }

        if ($entry->{races}) {
            my %races_with;
            foreach my $tag ($entry->{races}->@*) {
                $races_with{$_} = 1 for keys $race_tags{$tag}->%*;
            }

            # Don't list a function as having a race with itself (it
            # automatically does).
            delete $races_with{$function};

            if (keys %races_with) {
                my $race_text =
                    "${output_function_name}has potential races with other"
                  . " threads concurrently executing";
                my @race_names = sort name_order keys %races_with;
                if (@race_names == 1) {
                    $race_text .= " either itself or " . $race_names[0];
                }
                else {
                    $race_text .= " any of: itself, "
                            . join ", ", map { "$_()" } @race_names;
                    $race_text =~ s/, (*nla:.*,) /, or/x;
                }

                $race_text = wrap($columns, "", $hanging, "$race_text.");
                push @comments, split "\n", $race_text;
            }
        }

        if ($entry->{conditions}) {
            push @comments, "$function() locking macros are only valid if '"
                            . join(", ", $entry->{conditions}->@*)
                            . "'";
        }

        # Ready to output any comments
        if (@comments) {
            print $l "\n $dindent/* ", $comments[0];
            for (my $i = 1; $i < @comments; $i++) {
                print $l "\n $dindent * ", $comments[$i];
            }

            if (length($comments[-1]) + length($dindent) + 3
                                                           <= $comment_columns)
            {   # End the comment with a trailing "*/" if it fits on the line
                print $l " */\n";
            }
            else {  # Otherwise, put it on the next line
                print $l "\n $dindent */\n";
            }
        }

        # Now calculate and output the wrapper macros.
        my $need_exclusive = $entry->{races};

        if ($entry->{unsuitable}) {
            croak("Unsuitable function '$function' has a lock")
                                if $entry->{locks} || $entry->{categories};
            print $l <<~EOT;
                #${dindent}define ${FUNC}_LOCK                              \\
                #${dindent}  error_${function}_not_suitable_for_multi-threaded_operation
                EOT
        }
        elsif (! $entry->{locks} && ! $entry->{races} && ! $entry->{categories})
        {

            # No race, no lock => no op.
            print $l <<~EOT;
                #${dindent}define ${FUNC}_LOCK    NOOP
                #${dindent}define ${FUNC}_UNLOCK  NOOP
                EOT
        }
        else {

            # If we have a race but no other reason to lock, we do need a mutex;
            $need_exclusive = 1 if $entry->{races};

            my $locale_lock = delete $entry->{locks}{locale} // "";
            my $env_lock = delete $entry->{locks}{env} // "";

            # These are the other locks in the data.  Anything else is to catch
            # typos when someone makes a change to it.
            #
            # The ones marked 'x' override any input 'r' values.  These are
            # because the man pages are incomplete or inconsistent.  There
            # should be something that is a 'const:term' that locks term for
            # write-only access.  But there isn't, so have to assume that an
            # exclusive lock is needed.
            my %known_locks = (
                                hostid       => 'r',
                                term         => 'x',    # Obsolete
                                cwd          => 'x',    # Vulnerable to a
                                                        # chdir() call,
                                sigintr      => 'r',
                                mallopt      => 'r',
                                malloc_hooks => 'r',
                            );

            # This loop maps the rest of the locks into just the generic one
            my $generic_lock = "";
            my @unknown_locks;
            for my $key (keys $entry->{locks}->%*) {
                if (! defined $known_locks{$key}) {
                    push @unknown_locks, $key;
                    next;
                }

                # Can't get any more restrictive than this, so skip further
                # checking
                next if $generic_lock eq 'x';
                $generic_lock = $entry->{locks}{$key};
            }

            croak("Unknown lock: " . Dumper (\@unknown_locks))
                                                             if @unknown_locks;

            # If we need an exclusive lock, Look through the three locks for
            # one that already has an exclusive lock.  If so, we don't need to
            # force one
            for my $ref (\$locale_lock, \$env_lock, \$generic_lock) {
                if ($$ref eq 'x') {
                    $need_exclusive = 0;
                    last;
                }
            }

            # If there were no locks at all, but we still need an exclusive
            # lock, change the generic one to be one.
            $generic_lock = 'x' if $need_exclusive;

            $env_lock = 'ENV' . $env_lock if $env_lock;
            $generic_lock = 'GEN' . $generic_lock if $generic_lock;

            my $name = "";
            $name .= $generic_lock if $generic_lock;
            $name .= "_" if $env_lock && $generic_lock;
            $name .= $env_lock if $env_lock;

            # Ready to output if no locale issues are involved
            if (! $locale_lock && ! $entry->{categories}) {
                print $l <<~EOT;
                    #${dindent}define ${FUNC}_LOCK    ${name}_LOCK_
                    #${dindent}define ${FUNC}_UNLOCK  ${name}_UNLOCK_
                    EOT
            }
            else {
                my $cats = join "|", map { "${_}b_" } $entry->{categories}->@*;
                if ($name || $locale_lock) {
                    $name .= "_" if $name;
                    $locale_lock = "r" unless $locale_lock;
                    $name .= "LC$locale_lock";
                    print $l <<~EOT;
                        #${dindent}define ${FUNC}_LOCK    ${name}_LOCK_(  $cats)
                        #${dindent}define ${FUNC}_UNLOCK  ${name}_UNLOCK_($cats)
                        EOT
                }
                else {
                    print $l <<~EOT;
                        #${dindent}define ${FUNC}_LOCK    TSE_TOGGLE_(  $cats)
                        #${dindent}define ${FUNC}_UNLOCK  TSE_UNTOGGLE_($cats)
                        EOT
                }
                $name .= $locale_lock;

            }
        }
    }

    print $l "#  endif\n" if $functions{$function}->{entries}->@* > 1;

    print $l "#endif\n";

    delete $functions{$function};

}

read_only_bottom_close_and_rename($l);

if (%functions) {
    croak("These functions unhandled: " . join ", ", keys %functions);
}

# Below is the DATA section.  There are 5 types of lines:
#
#   1)  data lines, arranged like a table, with two columns, separated by a
#       pipe '|'.  The syntax is designed to be very similar to the ATTRIBUTES
#       section of the Linux man pages the data is derived from.  This allows
#       copy-pasting from those to here, with minimal changes, mostly
#       deletions.  There may be continuation lines for these, as described
#       below.
#   2)  a non-continuation line beginning with the string " __END__" indicates
#       it and anything past it to the end of the file are ignored.
#   2)  non-continuation, entirely blank lines are ignored
#   3)  non-continuation lines whose first non-blanks are the string "//" are
#       also ignored
#   4)  non-continuation lines beginning with the character '#' are treated as
#       C preprocessor lines, and output as-is, as part of the generated macro
#       definitions.
#
# The first column of a data line gives the functions that the second column
# applies to.  The functions are comma-separated.  See below for how this
# column can have continuation lines.
#
# The other column gives the data, again in the form of the Linux man pages.
# It applies to each function in the function list.  There are as many
# blank-separated fields as necessary in the second column.  If the final
# non-blank character on the line is '\', the next input line is a
# continuation line.
#
# If a continuation line contains the '|' character, the first portion of the
# line continues the functions column, and the second portion the data column.
# Otherwise, if the first character in the line is a blank, it continues the
# data column; if non-blank, it continues the functions column.   Continuation
# lines themselves may be continued, as many as necessary.
#
# The functions column may be continued even without a '\' character.  If the
# final non-blank character in the functions list is a comma, the next line is
# considered to be more functions, as many lines as necessary.

# The data column contains the following fields (appearing in any order,
# almost):
#
#   a)  Simply the character 'U'.  This indicates that the functions in the
#       functions column are thread-unsafe, and therefore should not be used in
#       multi-thread mode.  The presence of this field precludes any other
#       field but comment ones.
#
#   b)  The character 'M' means that the items in the functions column aren't
#       actually functions, but macros.  The only current practical effect of
#       this field is that each item is listed in the generated comments as
#       not being a function.
#
#   c)  The character 'V' means that the items in the functions column aren't
#       actually functions, but variables.  The only current practical effect
#       of this field is that each item is listed in the generated comments as
#       not being a function.
#
#   d)  The character 'X' means that the functions in the functions column are
#       non-Standard; they don't appear in any modern version of the POSIX
#       Standard.
#
#   e)  The character 'O' or that character followed by either a double-quote
#       enclosed "string" or a comma-separated list of function names.  This
#       means that the functions in the functions column in the first field
#       are considered obsolete.  If the 'O' stands alone, there is no simple
#       replacement for the obsolete functions.  If the 'O' is followed by a
#       comma-separated list, the list gives preferred alternatives that
#       should be used instead.  The "string" is displayed literally for
#       situations where a comma-separated list is inadequate.  "string" may
#       not contain the '"' character internally.
#
#   f)  The string "PF" followed by a name.  This means that the name is
#       preferred over the functions (symbolized by the 'P'), and that it
#       comes from a family (the 'F' means this) of Perl macros; 'name'
#       indicates which family
#
#   g)  The character 'P', followed by a comma-separated list of function
#       names (not beginning with 'F').  The functions in this list are
#       preferred over the function in the first-field functions column .

#   h)  The string "init".  This means that the functions in the functions
#       column are unsafe the first time they are called, but after that can
#       be made thread-safe by following the dictates of any remaining fields.
#       Hence these functions must be called at least once during
#       single-thread startup.
#
#   i)  The string "sig:" followed by the name of a signal.  For example
#       "sig:ALRM".  This means the functions are vulnerable to the SIGALRM
#       signal.  A list of all such functions is output in the comments at the
#       top of the generated header file, and individually at the point of the
#       macro definitions for each affected function.  But, it is beyond the
#       scope of this to automatically protect against these.  You'll have to
#       figure it out on your own.
#
#   j)  The string "timer".  This appears to be obsolete, with sig:ALRM taking
#       over its meaning.  The code here simply verifies that this string
#       doesn't appear without also "sig:ALRM"
#
#   k)  Any other string of \w characters, none uppercase.  For example,
#       "env".  Each function whose data line contains this field
#       non-atomically reads shared data of the same ilk.  So, in this case,
#       "env" means that these functions read from data associated with
#       "env".  Thus "env" serves as a tag that groups the functions into a
#       class of readers of whatever "env" means.
#
#       The implications of this is that these functions need to each be
#       protected by a read-lock associated with the tag, so that no function
#       that writes to that data can be concurrently executing.
#
#   l)  The string "const:" followed by a tag word (\w+).  This means that the
#       affected functions write to shared data associated with the tag.
#
#       The implication is that these functions need to each have an
#       exclusive lock associated with the tag, to avoid interference with
#       other such functions, or the functions in k) that have the same tag.
#       Continuing the previous example, the function putenv() has
#       "const:env".  This means it needs an exclusive lock on the mutex
#       associated with "env", and all functions that contain just "env" for
#       their data need read-locks on that mutex.
#
#   m)  The string "race".  This means that these each of these functions has
#       a potential race with something running in another thread.  If "race"
#       appears alone, what the other thing(s) that can interfere with it are
#       unspecified, but the generated header takes it as meaning the function
#       only has a race with another instance of it.  This could be because of
#       a buffer shared between threads, or simply that it returns a pointer
#       to internal global static storage, which must be used while still
#       locked, or copied to a per-thread safe place for later use.
#
#       "race" may be followed by a colon and a tag word, like "race:tmpbuf".
#       The potential race is with any other functions that also specify a
#       race with the same tag word.
#
#       The implication is that each such function must be protected with an
#       exclusive mutex associated with that tag, so none can run
#       concurrently.
#
#       A condition may be attached to a race, as in "race:mbrlen/!ps".  The
#       condition is introduced by a single '/'.  This means that the race
#       doesn't happen unless the condition is met.  If you look at the
#       mbrlen() man page, you will find that it takes an argument named "ps".
#       What the condition tells us is that any call to mbrlen with "!ps",
#       (hence ps is NULL) is thread-unsafe.  You can easily write your code
#       so that "ps" is non-NULL, and remove this cause of unsafety.  The
#       generated macros assume that you do so.
#
#   n)  A string giving a locale category, like "LC_TIME".  This indicates
#       what locale category affects the execution of this function.  Multiple
#       ones may be specified.  These are for future use. XXX
#
#   l)  The string "//".  This must be the final field on the line, and
#       the rest of the line becomes a comment string that is to be output
#       just above the generated macros for each affected function.  Any
#       continuation lines continue this comment.
#
# There is another type of continuation line.  If the last non-blank character
# in the functions column is a comma, there are more functions to come.  These
# come on the lines immediately following any data column continuation lines.
# These lines are simply more comma-separated function names.  The final line
# doesn't end in a comma.
#
# The #endif preprocessor line marks the end of the functions affected by
# previous preprocessor lines.  If there was no "#else" line, macros expanding
# to no-ops are automatically generated for the #else case.

__DATA__
addmntent  	| race:stream locale X
alphasort       | locale
asctime  	| race:asctime locale  OPerl_sv_strftime_tm
asctime_r  	| locale OPerl_sv_strftime_tm
asprintf, vasprintf| locale X
atof  	        | locale
atoi, atol, atoll| locale LC_NUMERIC
btowc           | LC_CTYPE
#ifndef __GLIBC__
basename        | race
#endif
#ifndef __GLIBC__
catgets         | race
#endif

catopen  	| env LC_MESSAGES
clearenv  	| const:env
clearerr_unlocked,| race:stream X                                           \
fflush_unlocked,  | // Is thread-safe if flockfile() or ftrylockfile() have \
fgetc_unlocked,   |    locked the stream, but should not be used since not  \
fgets_unlocked,   |    standardized and not widely implemented
fgetwc_unlocked,
fgetws_unlocked,
fputc_unlocked,
fputs_unlocked,
fputwc_unlocked,
fputws_unlocked,
fread_unlocked,
fwrite_unlocked,
getwc_unlocked,
putwc_unlocked

crypt_gensalt	| race:crypt_gensalt X
crypt       	| race:crypt
crypt_r       	| O

#ifndef __GLIBC__
ctermid         | race:ctermid/!s
#endif

ctermid_r       |
ctime_r  	| race:tzset env locale LC_TIME OPerl_sv_strftime_ints
ctime       	| race:tmbuf race:asctime race:tzset env locale LC_TIME     \
                  OPerl_sv_strftime_ints
cuserid  	| race:cuserid/!string locale

dbm_clearerr,   | race
dbm_close,
dbm_delete,
dbm_error,
dbm_fetch,
dbm_firstkey,
dbm_nextkey,
dbm_open,
dbm_store
#ifndef __GLIBC__
dirname         | locale
#endif
#ifndef __GLIBC__
dlerror         | race
#endif

drand48, erand48,| race:drand48
jrand48, lcong48,
lrand48, mrand48,
nrand48, seed48,
srand48

drand48_r,      | race:buffer X
erand48_r,
jrand48_r,
lcong48_r,
lrand48_r,
mrand48_r,
nrand48_r,
seed48_r,
srand48_r

ecvt        	| race:ecvt Osnprintf

encrypt, setkey | race:crypt
endaliasent  	| locale X

endfsent, 	| race:fsent X
setfsent

endgrent, 	| race:grent locale
setgrent

endgrent_r, 	| race:grent locale O X
setgrent_r

endhostent, 	| race:hostent env locale
sethostent

endhostent_r, 	| race:hostent env locale O X
sethostent_r

endnetent  	| race:netent env locale
endnetent_r  	| race:netent env locale O X

endnetgrent  	| race:netgrent X

endprotoent, 	| race:protoent locale
setprotoent

endprotoent_r, 	| race:protoent locale O X
setprotoent_r

endpwent,       | race:pwent locale
setpwent

endpwent_r,     | race:pwent locale O X
setpwent_r

endrpcent  	| locale X

endservent, 	| race:servent locale
setservent

endservent_r, 	| race:servent locale O X
setservent_r

endspent, 	| race:getspent locale X
getspent_r,
setspent

endttyent,      | race:ttyent X
getttyent,
getttynam,
setttyent

endusershell  	| U X
endutent        | race:utent Oendutxent X
endutxent       | race:utent
err  	        | locale X
error_at_line  	| race:error_at_line/error_one_per_line locale X
error       	| locale X
errx        	| locale X
ether_aton  	| U X
ether_ntoa  	| U X

execlp, execvp  | env
execvpe         | env X

exit        	| race:exit

__fbufsize, 	| race:stream X
__fpending,
__fsetlocking

__fpurge        | race:stream X

fcloseall  	| race:streams X
fcvt        	| race:fcvt Osnprintf
fgetgrent  	| race:fgetgrent X
fgetpwent  	| race:fgetpwent X
fgetspent  	| race:fgetspent X
fgetwc, getwc   | LC_CTYPE
fgetws          | LC_CTYPE
fnmatch  	| env locale
forkpty, openpty| locale X
putwc, fputwc   | LC_CTYPE
fputws          | LC_CTYPE
fts_children  	| U X
fts_read  	| U X
ftw             | race  Onftw

fwscanf, swscanf,| locale LC_NUMERIC
wscanf

gammaf, gammal  | race:signgam X 

gamma, lgammaf, | race:signgam
lgammal, lgamma

getaddrinfo  	| env locale
getaliasbyname_r| locale X
getaliasbyname  | U X Pgetaliasbyname_r
getaliasent_r  	| locale X
getaliasent  	| U X Pgetaliasent_r
getc_unlocked   | race:stream  // Is thread-safe if flockfile() or      \
                                  ftrylockfile() have locked the stream
getchar_unlocked| race:stdin  // Is thread-safe if flockfile() or       \
                                 ftrylockfile() have locked stdin

getcontext, setcontext| race:ucp

get_current_dir_name | env X
getdate_r  	| env locale LC_TIME X
getdate  	| race:getdate env locale LC_TIME

// On platforms where the static buffer contained in getenv() is per-thread
// rather than process-wide, another thread executing a getenv() at the same
// time won't destroy ours before we have copied the result safely away and
// unlocked the mutex.  On such platforms (which is most), we can have many
// readers of the environment at the same time.
#ifdef GETENV_PRESERVES_OTHER_THREAD
getenv 	        | env
secure_getenv   | X env
#else
// If, on the other hand, another thread could zap our getenv() return, we
// need to keep them from executing until we are done
getenv 	| race env
secure_getenv   | X race env
#endif

getfsent, 	| race:fsent locale X
getfsfile,
getfsspec

getgrent  	| race:grent race:grentbuf locale
getgrent_r  	| race:grent locale X
getgrgid  	| race:grgid locale
getgrgid_r  	| locale
getgrnam  	| race:grnam locale
getgrnam_r  	| locale
getgrouplist  	| locale X
gethostbyaddr_r | env locale X
gethostbyaddr  	| race:hostbyaddr env locale Ogetaddrinfo                   \
                  // return needs a deep copy for safety
gethostbyname2_r| env locale X
gethostbyname2  | race:hostbyname2 env locale X
gethostbyname_r | env locale X
gethostbyname  	| race:hostbyname env locale Ogetnameinfo                   \
                  // return needs a deep copy for safety
gethostent      | race:hostent race:hostentbuf env locale
gethostent_r    | race:hostent env locale
gethostid  	| hostid env locale
getlogin  	| race:getlogin race:utent sig:ALRM timer locale
getlogin_r  	| race:utent sig:ALRM timer locale
getmntent_r  	| locale X
getmntent  	| race:mntentbuf locale X
getnameinfo  	| env locale
getnetbyaddr_r  | locale X
getnetbyaddr  	| race:netbyaddr locale
getnetbyname_r  | locale X
getnetbyname  	| race:netbyname env locale
getnetent_r  	| locale X
getnetent  	| race:netent race:netentbuf env locale
getnetgrent  	| race:netgrent race:netgrentbuf locale X

getnetgrent_r, 	| race:netgrent locale X
innetgr,
setnetgrent

getopt  	| race:getopt env

getopt_long,    | race:getopt env X
getopt_long_only

getpass  	| term  O"DO NOT USE" X
getprotobyname_r| locale X
getprotobyname  | race:protobyname locale
getprotobynumber_r| locale X
getprotobynumber| race:protobynumber locale
getprotoent_r  	| locale X
getprotoent  	| race:protoent race:protoentbuf locale
getpwent  	| race:pwent race:pwentbuf locale
getpwent_r  	| race:pwent locale X
getpw       	| locale Ogetpwuid X
getpwnam_r  	| locale
getpwnam  	| race:pwnam locale
getpwuid_r  	| locale
getpwuid  	| race:pwuid locale
getrpcbyname_r  | locale X
getrpcbyname  	| U X Pgetrpcbyname_r
getrpcbynumber_r| locale X
getrpcbynumber  | U X Pgetrpcbynumber_r
getrpcent_r  	| locale X
getrpcent  	| U X Pgetrpcent_r
getrpcport  	| env locale X
getservbyname_r | locale X
getservbyname  	| race:servbyname locale
getservbyport_r | locale X
getservbyport  	| race:servbyport locale
getservent_r  	| locale X
getservent  	| race:servent race:serventbuf locale
getspent  	| race:getspent race:spentbuf locale X
getspnam  	| race:getspnam locale X
getspnam_r  	| locale X
getusershell  	| U X
getutent        | init race:utent race:utentbuf sig:ALRM timer Ogetutxent X
getutxent       | init race:utent race:utentbuf sig:ALRM timer
getutid         | init race:utent sig:ALRM timer Ogetutxid X
getutxid        | init race:utent sig:ALRM timer
getutline  	| init race:utent sig:ALRM timer Ogetutxline X
getutxline  	| init race:utent sig:ALRM timer
getwchar        | LC_CTYPE
getwchar_unlocked| race:stdin X                                             \
                    // Is thread-safe if flockfile() or ftrylockfile()      \
                       have locked stdin, but should not be used since not  \
                       standardized and not widely implemented

glob  	        | race:utent env sig:ALRM timer locale LC_COLLATE
gmtime_r  	| env locale
gmtime 	        | race:tmbuf env locale

grantpt  	| locale

hcreate,  	| race:hsearch
hdestroy,
hsearch

hcreate_r,      | race:htab X
hsearch_r,
hdestroy_r

iconv_open  	| locale
iconv       	| race:cd

inet_addr,      | locale
inet_ntoa

inet_aton, 	| locale X
inet_network

inet_ntop  	| locale
inet_pton  	| locale
initgroups  	| locale X

initstate_r,    | race:buf X
random_r,
setstate_r,
srandom_r

iruserok_af  	| locale X
iruserok  	| locale X
isalpha         | LC_CTYPE PFisALPHA
isalnum         | LC_CTYPE PFisALNUM
isascii         | LC_CTYPE  PFisASCII                                       \
                  // Considered obsolete as being non-portable, but Perl    \
                     makes it portable when using a macro
isblank         | LC_CTYPE PFisBLANK
iscntrl         | LC_CTYPE PFisCNTRL
isdigit         | LC_CTYPE PFisDIGIT
isgraph         | LC_CTYPE PFisGRAPH
islower         | LC_CTYPE PFisLOWER
isprint         | LC_CTYPE PFisPRINT
ispunct         | LC_CTYPE PFisPUNCT
isspace         | LC_CTYPE PFisSPACE
isupper         | LC_CTYPE PFisUPPER
isxdigit        | LC_CTYPE PFisXDIGIT

isalnum_l,      | LC_CTYPE
isalpha_l,
isblank_l, iscntrl_l,
isdigit_l, isgraph_l,
islower_l, isprint_l,
ispunct_l, isspace_l,
isupper_l, isxdigit_l
isascii_l       | LC_CTYPE X

iswalpha        | locale LC_CTYPE PFisALPHA
iswalnum        | locale LC_CTYPE PFisALNUM
iswblank        | locale LC_CTYPE PFisBLANK
iswcntrl        | locale LC_CTYPE PFisCNTRL
iswdigit        | locale LC_CTYPE PFisDIGIT
iswgraph        | locale LC_CTYPE PFisGRAPH
iswlower        | locale LC_CTYPE PFisLOWER
iswprint        | locale LC_CTYPE PFisPRINT
iswpunct        | locale LC_CTYPE PFisPUNCT
iswspace        | locale LC_CTYPE PFisSPACE
iswupper        | locale LC_CTYPE PFisUPPER
iswxdigit       | locale LC_CTYPE PFisXDIGIT

iswalnum_l,     | locale LC_CTYPE
iswalpha_l, iswblank_l,
iswcntrl_l, iswdigit_l,
iswgraph_l, iswlower_l,
iswprint_l, iswpunct_l,
iswspace_l, iswupper_l,
iswxdigit_l

l64a  	        | race:l64a
localeconv  	| race:localeconv locale LC_NUMERIC LC_MONETARY PPerl_localeconv
localtime       | race:tmbuf race:tzset env locale
localtime_r  	| race:tzset env locale
login, logout  	| race:utent sig:ALRM timer X
login_tty  	| race:ttyname X
logwtmp  	| sig:ALRM timer X
makecontext     | race:ucp
mallinfo  	| init const:mallopt X
MB_CUR_MAX      | M LC_CTYPE
mblen  	        | race LC_CTYPE Pmbrlen
mbrlen  	| race:mbrlen/!ps LC_CTYPE
mbrtowc         | LC_CTYPE race:mbrtowc/!ps
mbsinit         | LC_CTYPE
mbsnrtowcs  	| race:mbsnrtowcs/!ps LC_CTYPE
mbsrtowcs  	| race:mbsrtowcs/!ps LC_CTYPE
mbstowcs        | LC_CTYPE
mbtowc          | race LC_CTYPE Pmbrtowc

mcheck_check_all,| race:mcheck const:malloc_hooks X
mcheck_pedantic,
mcheck, mprobe

mktime  	| race:tzset env locale
mtrace, muntrace| U X
nan, nanf, nanl | locale
nftw        	| cwd   // chdir() in another thread will mess this up
newlocale  	| env
nl_langinfo  	| race locale
perror  	| race:stderr
posix_fallocate | // The safety in glibc depends on the file system.    \
                     Generally safe

printf, fprintf,| LC_NUMERIC locale
dprintf, sprintf,
snprintf, vprintf,
vfprintf, vdprintf,
vsprintf, vsnprintf
profil  	| U X
psiginfo  	| locale
psignal  	| locale
ptsname  	| race:ptsname
putc_unlocked   | race:stream  // Is thread-safe if flockfile() or          \
                                  ftrylockfile() have locked the stream
putchar_unlocked| race:stdout  // Is thread-safe if flockfile() or          \
                                  ftrylockfile() have locked stdin
putenv  	| const:env
putpwent  	| locale
putspent  	| locale X
pututline       | race:utent sig:ALRM timer Opututxline X
pututxline      | race:utent sig:ALRM timer
putwchar        | LC_CTYPE
putwchar_unlocked| race:stdout X  // Is thread-safe if flockfile() or       \
                                     ftrylockfile() have locked stdout, but \
                                     should not be used since not           \
                                     standardized and not widely implemented
valloc, pvalloc | init X
qecvt  	        | race:qecvt Osnprintf X
qfcvt       	| race:qfcvt Osnprintf X

#ifndef __GLIBC__
rand            | // Problematic and should be avoided; See POSIX Standard
#endif

rcmd_af  	| U X
rcmd        	| U X
readdir  	| race:dirstream
readdir_r       | Oreaddir  // Deprecated by glibc.  It is recommended to   \
                               use plain readdir() instead due to various   \
                               limitations, and modern implementations of   \
                               readdir tend to be thread-safe if concurrent \
                               calls use different directory streams
readdir64       | race:dirstream
readdir64_r     |
re_comp         | U  Oregcomp X
re_exec  	| U  Oregexec X
regcomp  	| locale
regerror  	| env
regexec  	| locale
res_nclose  	| locale X
res_ninit  	| locale X
res_nquerydomain| locale X
res_nquery  	| locale X
res_nsearch  	| locale X
res_nsend  	| locale X
rexec_af  	| U  Orcmd X
rexec  	        | U  Orcmd X
rpmatch         | LC_MESSAGES locale X
ruserok_af  	| locale X
ruserok  	| locale X

scanf, fscanf,  | locale LC_NUMERIC
sscanf, vscanf,
vsscanf, vfscanf

setaliasent  	| locale X
setenv, unsetenv| const:env
sethostid  	| const:hostid

#ifndef WIN32
setlocale  	| race const:locale env PPerl_setlocale
setlocale_r  	| const:locale env O X PPerl_setlocale
#endif

setlogmask  	| race:LogMask
setnetent  	| race:netent env locale
setnetent_r  	| race:netent env locale O X
setrpcent  	| locale X
setusershell  	| U X
setutent        | race:utent Osetutxent X
setutxent       | race:utent
sgetspent  	| race:sgetspent X
sgetspent_r  	| locale X
shm_open, shm_unlink| locale
siginterrupt  	| const:sigintr                                             \
                  O"Use sigaction(2) with the SA_RESTART flag instead"
sleep       	| sig:SIGCHLD/linux
ssignal  	| sigintr O X

strcasecmp,     | locale LC_CTYPE LC_COLLATE                                \
strncasecmp     | // The POSIX Standard says results are undefined unless   \
                     LC_CTYPE is the POSIX locale

strcasestr  	| locale X
strcoll, wcscoll| locale LC_COLLATE

strerror        | race:strerror LC_MESSAGES

strerror_r,     | LC_MESSAGES
strerror_l

strfmon         | LC_MONETARY locale
strfmon_l       | LC_MONETARY

strfromd,       | locale LC_NUMERIC  // Asynchronous unsafe
strfromf, strfroml

strftime  	| race:tzset env locale LC_TIME                             \
                  PPerl_sv_strftime_tm,Perl_sv_strftime_ints

strftime_l  	| LC_TIME
strptime  	| env locale LC_TIME
strsignal  	| race:strsignal locale LC_MESSAGES

strtod,         | locale LC_NUMERIC
strtof,
strtold

strtoimax  	| locale
strtok  	| race:strtok Pstrtok_r
wcstod, wcstold,| locale LC_NUMERIC
wcstof

strtol, strtoll | locale LC_NUMERIC
strtoq, strtouq | locale LC_NUMERIC X
strtoul, strtoull| locale LC_NUMERIC


strtoumax  	| locale
strverscmp      | LC_COLLATE X
strxfrm  	| locale LC_COLLATE LC_CTYPE
wcsxfrm         | locale LC_COLLATE LC_CTYPE
swapcontext  	| race:oucp race:ucp
sysconf  	| env

#ifndef __GLIBC__
system          | // Some implementations are not-thread safe; See POSIX    \
                     Standard
#endif

syslog          | env locale

tdelete, 	| race:rootp
tfind,
tsearch

tempnam  	| env Omkstemp,tmpfile
timegm  	| env locale X
timelocal  	| env locale X
tmpnam  	| race:tmpnam/!s Omkstemp,tmpfile
tmpnam_r  	| Omkstemp,tmpfile X
tolower, tolower_l| LC_CTYPE PFtoLOWER
toupper, toupper_l| LC_CTYPE PFtoUPPER
towctrans       | LC_CTYPE
towlower, towlower_l| LC_CTYPE PFtoLOWER
towupper, towupper_l| LC_CTYPE PFtoUPPER
ttyname  	| race:ttyname  Pttyname_r 
ttyname_r  	|
ttyslot  	| U X
twalk  	        | race:root
twalk_r  	| race:root X

// The POSIX Standard says:
//
//    "If a thread accesses tzname, daylight, or timezone  directly while
//     another thread is in a call to tzset(), or to any function that is
//     required or allowed to set timezone information as if by calling tzset(),
//     the behavior is undefined."
//
// Those three items are names of (typically) global variables.
//
//  Further,
//
//    "The tzset() function shall use the value of the environment variable TZ
//     to set time conversion information used by ctime, localtime, mktime, and
//     strftime. If TZ is absent from the environment, implementation-defined
//     default timezone information shall be used.
//
// This means that tzset() must have an exclusive lock, as well as the others
// listed that call it.
tzset  	        | race:tzset env locale
tzname, daylight,| V race:tzset
timezone

ungetwc         | LC_CTYPE
updwtmp  	| sig:ALRM timer X
utmpname  	| race:utent X

// khw believes that this function is thread-safe if called with a per-thread
// argument
va_arg  	| race:ap/arg-ap-is-local-to-its-thread

verr  	        | locale X
verrx       	| locale X
versionsort     | locale X
vsyslog         | env locale X
vwarn       	| locale X
vwarnx  	| locale X
warn        	| locale X
warnx       	| locale X
wcrtomb  	| race:wcrtomb/!ps LC_CTYPE
wcscasecmp  	| locale LC_CTYPE
wcsncasecmp  	| locale LC_CTYPE
wcsnrtombs  	| race:wcsnrtombs/!ps LC_CTYPE
wcsrtombs  	| race:wcsrtombs/!ps LC_CTYPE
wcstoimax  	| locale
wcstombs        | LC_CTYPE
wcstoumax  	| locale
wcswidth  	| locale LC_CTYPE
wctob           | LC_CTYPE  Pwctomb,wcrtomb
wctomb  	| race LC_CTYPE Pwcrtomb
wctrans  	| locale LC_CTYPE
wctype  	| locale LC_CTYPE
wcwidth  	| locale LC_CTYPE
wordexp  	| race:utent const:env sig:ALRM timer locale
wprintf, fwprintf,| locale LC_CTYPE LC_NUMERIC
swprintf, vwprintf,
vfwprintf, vswprintf
scandir         | LC_CTYPE LC_COLLATE
wcschr          | LC_CTYPE
wcsftime        | LC_CTYPE LC_TIME
wcsrchr         | LC_CTYPE

__END__

The relevant parts of many of the man page sources for the above data.  Kept
here as a convenience for checking things

       │l64a()    │ Thread safety │ MT-Unsafe race:l64a │
       │asprintf(), vasprintf() │ Thread safety │ MT-Safe locale │
       │atof()    │ Thread safety │ MT-Safe locale │
       ├────────────────────────┼───────────────┼────────────────┤
       │atoi(), atol(), atoll() │ Thread safety │ MT-Safe locale │
       │bindresvport() │ Thread safety │ glibc >= 2.17: MT-Safe  │
       │               │               │ glibc < 2.17: MT-Unsafe │
       ├──────────┼───────────────┼─────────────────────┤
       │catopen()  │ Thread safety │ MT-Safe env │
       ├──────────┼───────────────┼─────────────────────┤
       │cfree()   │ Thread safety │ MT-Safe // In glibc  │
       ├──────────┼───────────────┼─────────────────────┤
       │clearenv() │ Thread safety │ MT-Unsafe const:env │
       ├──────────────────┼───────────────┼──────────────────────────────┤
       │crypt              │ Thread safety │ MT-Unsafe race:crypt │
       ├──────────────────┼───────────────┼──────────────────────────────┤
       │crypt_gensalt     │ Thread safety │ MT-Unsafe race:crypt_gensalt │
       ├──────────────────┼───────────────┼──────────────────────────────┤
       │asctime()      │ Thread safety │ MT-Unsafe race:asctime locale   │
       ├───────────────┼───────────────┼─────────────────────────────────┤
       │asctime_r()    │ Thread safety │ MT-Safe locale                  │
       ├───────────────┼───────────────┼─────────────────────────────────┤
       │ctime()        │ Thread safety │ MT-Unsafe race:tmbuf            │
       │               │               │ race:asctime env locale         │
       ├───────────────┼───────────────┼─────────────────────────────────┤
       │ctime_r(), gm‐ │ Thread safety │ MT-Safe env locale              │
       │time_r(), lo‐  │               │                                 │
       │caltime_r(),   │               │                                 │
       │mktime()       │               │                                 │
       ├───────────────┼───────────────┼─────────────────────────────────┤
       │gmtime(), lo‐  │ Thread safety │ MT-Unsafe race:tmbuf env locale │
       │caltime()      │               │                                 │
       ├──────────────────────┼───────────────┼────────────────────────┤
       │drand48(), erand48(), │ Thread safety │ MT-Unsafe race:drand48 │
       │lrand48(), nrand48(), │               │                        │
       │mrand48(), jrand48(), │               │                        │
       │srand48(), seed48(),  │               │                        │
       │lcong48()             │               │                        │
       ├──────────────────────────┼───────────────┼─────────────────────┤
       │drand48_r(), erand48_r(), │ Thread safety │ MT-Safe race:buffer │
       │lrand48_r(), nrand48_r(), │               │                     │
       │mrand48_r(), jrand48_r(), │               │                     │
       │srand48_r(), seed48_r(),  │               │                     │
       │lcong48_r()               │               │                     │
       ├──────────────────────────┼───────────────┼─────────────────────┤
       │ecvt()    │ Thread safety │ MT-Unsafe race:ecvt │
       ├──────────┼───────────────┼─────────────────────┤
       │fcvt()    │ Thread safety │ MT-Unsafe race:fcvt │
       ├──────────────────────────┼───────────────┼─────────────────────┤
       │encrypt(), setkey()     │ Thread safety │ MT-Unsafe race:crypt │
       ├──────────────────┼───────────────┼────────────────┤
       │err(), errx(),    │ Thread safety │ MT-Safe locale │
       │warn(), warnx(),  │               │                │
       │verr(), verrx(),  │               │                │
       │vwarn(), vwarnx() │               │                │
       ├────────────────┼───────────────┼───────────────────────────────────┤
       │error()         │ Thread safety │ MT-Safe locale                    │
       ├────────────────┼───────────────┼───────────────────────────────────┤
       │error_at_line() │ Thread safety │ MT-Unsafe race:error_at_line/er‐  │
       │                │               │ ror_one_per_line locale           │
       ├──────────────────────────────────┼───────────────┼───────────┤
       │ether_aton(), ether_ntoa()        │ Thread safety │ MT-Unsafe │
       ├──────────────────────────────┼───────────────┼─────────────┤
       │execlp(), execvp(), execvpe() │ Thread safety │ MT-Safe env │
       ├──────────┼───────────────┼─────────────────────┤
       │exit()    │ Thread safety │ MT-Unsafe race:exit │
       ├──────────────────────────┼───────────────┼─────────────────────┤
       │fcloseall() │ Thread safety │ MT-Unsafe race:streams │
       ├──────────────────────────┼───────────────┼─────────────────────┤
       │fgetgrent() │ Thread safety │ MT-Unsafe race:fgetgrent │
       ├────────────┼───────────────┼──────────────────────────┤
       │fgetpwent() │ Thread safety │ MT-Unsafe race:fgetpwent │
       ├──────────────────────────┼───────────────┼─────────────────────┤
       │fmtmsg()  │ Thread safety │ glibc >= 2.16: MT-Safe  │
       │          │               │ glibc < 2.16: MT-Unsafe │
       ├──────────┼───────────────┼────────────────────┤
       │fnmatch() │ Thread safety │ MT-Safe env locale │
       ├───────────┼───────────────┼─────────────────────┤
       │__fpurge() │ Thread safety │ MT-Safe race:stream │
       ├───────────────────────────────────┼───────────────┼───────────┤
       │fts_read(), fts_children()         │ Thread safety │ MT-Unsafe │
       ├──────────┼───────────────┼─────────────┤
       │nftw()    │ Thread safety │ MT-Safe cwd │
       ├────────────────────────────┼───────────────┼────────────────────────┤
       │gamma(), gammaf(), gammal() │ Thread safety │ MT-Unsafe race:signgam │
       ├────────────────┼───────────────┼────────────────────┤
       │getaddrinfo()   │ Thread safety │ MT-Safe env locale │
       ├───────────────────────────┼───────────────┼──────────────────┤
       │getcontext(), setcontext() │ Thread safety │ MT-Safe race:ucp │
       ├───────────────────────┼───────────────┼─────────────┤
       │get_current_dir_name() │ Thread safety │ MT-Safe env │
       ├────────────┼───────────────┼───────────────────────────────────┤
       │getdate()   │ Thread safety │ MT-Unsafe race:getdate env locale │
       ├────────────┼───────────────┼───────────────────────────────────┤
       │getdate_r() │ Thread safety │ MT-Safe env locale                │
       ├──────────────────────────┼───────────────┼─────────────┤
       │getenv(), secure_getenv() │ Thread safety │ MT-Safe env │
       ├─────────────┼───────────────┼─────────────────────────────┤
       │endfsent(),  │ Thread safety │ MT-Unsafe race:fsent        │
       │setfsent()   │               │                             │
       ├─────────────┼───────────────┼─────────────────────────────┤
       │getfsent(),  │ Thread safety │ MT-Unsafe race:fsent locale │
       │getfsspec(), │               │                             │
       │getfsfile()  │               │                             │
       ├──────────────────────────┼───────────────┼─────────────────────┤
       │getgrent()  │ Thread safety │ MT-Unsafe race:grent        │
       │            │               │ race:grentbuf locale        │
       ├────────────┼───────────────┼─────────────────────────────┤
       │setgrent(), │ Thread safety │ MT-Unsafe race:grent locale │
       │endgrent()  │               │                             │
       ├──────────────────────────┼───────────────┼─────────────────────┤
       │getgrent_r()  │ Thread safety │ MT-Unsafe race:grent locale │
       ├──────────────┼───────────────┼─────────────────────────────┤
       │getgrnam()    │ Thread safety │ MT-Unsafe race:grnam locale │
       ├──────────────┼───────────────┼─────────────────────────────┤
       │getgrgid()    │ Thread safety │ MT-Unsafe race:grgid locale │
       ├──────────────┼───────────────┼─────────────────────────────┤
       │getgrnam_r(), │ Thread safety │ MT-Safe locale              │
       │getgrgid_r()  │               │                             │
       ├───────────────┼───────────────┼────────────────┤
       │getgrouplist() │ Thread safety │ MT-Safe locale │
       ├───────────────────┼───────────────┼───────────────────────────────┤
       │gethostbyname()    │ Thread safety │ MT-Unsafe race:hostbyname env │
       │                   │               │ locale                        │
       ├───────────────────┼───────────────┼───────────────────────────────┤
       │gethostbyaddr()    │ Thread safety │ MT-Unsafe race:hostbyaddr env │
       │                   │               │ locale                        │
       ├───────────────────┼───────────────┼───────────────────────────────┤
       │sethostent(),      │ Thread safety │ MT-Unsafe race:hostent env    │
       │endhostent(),      │               │ locale                        │
       │gethostent_r()     │               │                               │
       ├───────────────────┼───────────────┼───────────────────────────────┤
       │gethostent()       │ Thread safety │ MT-Unsafe race:hostent        │
       │                   │               │ race:hostentbuf env locale    │
       ├───────────────────┼───────────────┼───────────────────────────────┤
       │gethostbyname2()   │ Thread safety │ MT-Unsafe race:hostbyname2    │
       │                   │               │ env locale                    │
       ├───────────────────┼───────────────┼───────────────────────────────┤
       │gethostbyaddr_r(), │ Thread safety │ MT-Safe env locale            │
       │gethostbyname_r(), │               │                               │
       │gethostbyname2_r() │               │                               │
       ├──────────────────────────┼───────────────┼─────────────────────┤
       │gethostid() │ Thread safety │ MT-Safe hostid env locale │
       ├────────────┼───────────────┼───────────────────────────┤
       │sethostid() │ Thread safety │ MT-Unsafe const:hostid    │
       ├──────────────────────────┼───────────────┼─────────────────────┤
       │getlogin()   │ Thread safety │ MT-Unsafe race:getlogin race:utent    │
       │             │               │ sig:ALRM timer locale                 │
       ├─────────────┼───────────────┼───────────────────────────────────────┤
       │getlogin_r() │ Thread safety │ MT-Unsafe race:utent sig:ALRM timer   │
       │             │               │ locale                                │
       ├─────────────┼───────────────┼───────────────────────────────────────┤
       │cuserid()    │ Thread safety │ MT-Unsafe race:cuserid/!string locale │
       ├──────────────────────────┼───────────────┼─────────────────────┤
       │getmntent()   │ Thread safety │ MT-Unsafe race:mntentbuf locale │
       ├──────────────┼───────────────┼─────────────────────────────────┤
       │addmntent()   │ Thread safety │ MT-Safe race:stream locale      │
       ├──────────────┼───────────────┼─────────────────────────────────┤
       │getmntent_r() │ Thread safety │ MT-Safe locale                  │
       ├──────────────────────────┼───────────────┼─────────────────────┤
       │getnameinfo() │ Thread safety │ MT-Safe env locale │
       ├───────────────┼───────────────┼───────────────────────────┤
       │getnetent()    │ Thread safety │ MT-Unsafe race:netent     │
       │               │               │ race:netentbuf env locale │
       ├───────────────┼───────────────┼───────────────────────────┤
       │getnetbyname() │ Thread safety │ MT-Unsafe race:netbyname  │
       │               │               │ env locale                │
       ├───────────────┼───────────────┼───────────────────────────┤
       │getnetbyaddr() │ Thread safety │ MT-Unsafe race:netbyaddr  │
       │               │               │ locale                    │
       ├───────────────┼───────────────┼───────────────────────────┤
       │setnetent(),   │ Thread safety │ MT-Unsafe race:netent env │
       │endnetent()    │               │ locale                    │
       ├──────────────────┼───────────────┼────────────────┤
       │getnetent_r(),    │ Thread safety │ MT-Safe locale │
       │getnetbyname_r(), │               │                │
       │getnetbyaddr_r()  │               │                │
       ├─────────────────────────┼───────────────┼───────────────────────────┤
       │getopt(), getopt_long(), │ Thread safety │ MT-Unsafe race:getopt env │
       │getopt_long_only()       │               │                           │
       ├──────────┼───────────────┼────────────────┤
       │getpass() │ Thread safety │ MT-Unsafe term │
       ├───────────────────┼───────────────┼──────────────────────────────┤
       │getprotoent()      │ Thread safety │ MT-Unsafe race:protoent      │
       │                   │               │ race:protoentbuf locale      │
       ├───────────────────┼───────────────┼──────────────────────────────┤
       │getprotobyname()   │ Thread safety │ MT-Unsafe race:protobyname   │
       │                   │               │ locale                       │
       ├───────────────────┼───────────────┼──────────────────────────────┤
       │getprotobynumber() │ Thread safety │ MT-Unsafe race:protobynumber │
       │                   │               │ locale                       │
       ├───────────────────┼───────────────┼──────────────────────────────┤
       │setprotoent(),     │ Thread safety │ MT-Unsafe race:protoent      │
       │endprotoent()      │               │ locale                       │
       ├─────────────────────┼───────────────┼────────────────┤
       │getprotoent_r(),     │ Thread safety │ MT-Safe locale │
       │getprotobyname_r(),  │               │                │
       │getprotobynumber_r() │               │                │
       ├──────────┼───────────────┼────────────────┤
       │getpw()   │ Thread safety │ MT-Safe locale │
       ├────────────┼───────────────┼─────────────────────────────┤
       │getpwent()  │ Thread safety │ MT-Unsafe race:pwent        │
       │            │               │ race:pwentbuf locale        │
       ├────────────┼───────────────┼─────────────────────────────┤
       │setpwent(), │ Thread safety │ MT-Unsafe race:pwent locale │
       │endpwent()  │               │                             │
       ├──────────────┼───────────────┼─────────────────────────────┤
       │getpwent_r()  │ Thread safety │ MT-Unsafe race:pwent locale │
       ├──────────────┼───────────────┼─────────────────────────────┤
       │getpwnam()    │ Thread safety │ MT-Unsafe race:pwnam locale │
       ├──────────────┼───────────────┼─────────────────────────────┤
       │getpwuid()    │ Thread safety │ MT-Unsafe race:pwuid locale │
       ├──────────────┼───────────────┼─────────────────────────────┤
       │getpwnam_r(), │ Thread safety │ MT-Safe locale              │
       │getpwuid_r()  │               │                             │
       ├─────────────────────────────┼───────────────┼────────────────┤
       │getrpcent(), getrpcbyname(), │ Thread safety │ MT-Unsafe      │
       │getrpcbynumber()             │               │                │
       ├─────────────────────────────┼───────────────┼────────────────┤
       │setrpcent(), endrpcent()     │ Thread safety │ MT-Safe locale │
       ├────────────────────┼───────────────┼────────────────┤
       │getrpcent_r(),      │ Thread safety │ MT-Safe locale │
       │getrpcbyname_r(),   │               │                │
       │getrpcbynumber_r()  │               │                │
       ├─────────────┼───────────────┼────────────────────┤
       │getrpcport() │ Thread safety │ MT-Safe env locale │
       ├────────────────┼───────────────┼───────────────────────────┤
       │getservent()    │ Thread safety │ MT-Unsafe race:servent    │
       │                │               │ race:serventbuf locale    │
       ├────────────────┼───────────────┼───────────────────────────┤
       │getservbyname() │ Thread safety │ MT-Unsafe race:servbyname │
       │                │               │ locale                    │
       ├────────────────┼───────────────┼───────────────────────────┤
       │getservbyport() │ Thread safety │ MT-Unsafe race:servbyport │
       │                │               │ locale                    │
       ├────────────────┼───────────────┼───────────────────────────┤
       │setservent(),   │ Thread safety │ MT-Unsafe race:servent    │
       │endservent()    │               │ locale                    │
       ├───────────────────┼───────────────┼────────────────┤
       │getservent_r(),    │ Thread safety │ MT-Safe locale │
       │getservbyname_r(), │               │                │
       │getservbyport_r()  │               │                │
       ├──────────────┼───────────────┼────────────────────────────────┤
       │getspnam()    │ Thread safety │ MT-Unsafe race:getspnam locale │
       ├──────────────┼───────────────┼────────────────────────────────┤
       │getspent()    │ Thread safety │ MT-Unsafe race:getspent        │
       │              │               │ race:spentbuf locale           │
       ├──────────────┼───────────────┼────────────────────────────────┤
       │setspent(),   │ Thread safety │ MT-Unsafe race:getspent locale │
       │endspent(),   │               │                                │
       │getspent_r()  │               │                                │
       ├──────────────┼───────────────┼────────────────────────────────┤
       │fgetspent()   │ Thread safety │ MT-Unsafe race:fgetspent       │
       ├──────────────┼───────────────┼────────────────────────────────┤
       │sgetspent()   │ Thread safety │ MT-Unsafe race:sgetspent       │
       ├──────────────┼───────────────┼────────────────────────────────┤
       │putspent(),   │ Thread safety │ MT-Safe locale                 │
       │getspnam_r(), │               │                                │
       │sgetspent_r() │               │                                │
       ├──────────────┼───────────────┼────────────────────────────────┤
       │getttyent(), setttyent(), │ Thread safety │ MT-Unsafe race:ttyent │
       │endttyent(), getttynam()  │               │                       │
       ├────────────────────────────────┼───────────────┼───────────┤
       │getusershell(), setusershell(), │ Thread safety │ MT-Unsafe │
       │endusershell()                  │               │           │
       ├────────────┼───────────────┼──────────────────────────────┤
       │getutent()  │ Thread safety │ MT-Unsafe init race:utent    │
       │            │               │ race:utentbuf sig:ALRM timer │
       ├────────────┼───────────────┼──────────────────────────────┤
       │getutid(),  │ Thread safety │ MT-Unsafe init race:utent    │
       │getutline() │               │ sig:ALRM timer               │
       ├────────────┼───────────────┼──────────────────────────────┤
       │pututline() │ Thread safety │ MT-Unsafe race:utent         │
       │            │               │ sig:ALRM timer               │
       ├────────────┼───────────────┼──────────────────────────────┤
       │setutent(), │ Thread safety │ MT-Unsafe race:utent         │
       │endutent(), │               │                              │
       │utmpname()  │               │                              │
       ├───────────┼───────────────┼──────────────────────────┤
       │glob()     │ Thread safety │ MT-Unsafe race:utent env │
       │           │               │ sig:ALRM timer locale    │
       ├───────────┼───────────────┼──────────────────────────┤
       │grantpt() │ Thread safety │ MT-Safe locale │
       ├──────────┼───────────────┼─────────────────┤
       │ssignal() │ Thread safety │ MT-Safe sigintr │
       ├──────────────────────────┼───────────────┼────────────────────────┤
       │hcreate(), hsearch(),     │ Thread safety │ MT-Unsafe race:hsearch │
       │hdestroy()                │               │                        │
       ├──────────────────────────┼───────────────┼────────────────────────┤
       │hcreate_r(), hsearch_r(), │ Thread safety │ MT-Safe race:htab      │
       │hdestroy_r()              │               │                        │
       ├──────────┼───────────────┼─────────────────┤
       │iconv()   │ Thread safety │ MT-Safe race:cd │
       ├─────────────┼───────────────┼────────────────┤
       │iconv_open() │ Thread safety │ MT-Safe locale │
       ├───────────────────────────────┼───────────────┼────────────────┤
       │inet_aton(), inet_addr(),      │ Thread safety │ MT-Safe locale │
       │inet_network(), inet_ntoa()    │               │                │
       ├───────────────────────────────┼───────────────┼────────────────┤
       │inet_ntop() │ Thread safety │ MT-Safe locale │
       │inet_pton() │ Thread safety │ MT-Safe locale │
       ├─────────────┼───────────────┼────────────────┤
       │initgroups() │ Thread safety │ MT-Safe locale │
       ├───────────┼───────────────┼────────────────┤
       │iswalnum() │ Thread safety │ MT-Safe locale │
       ├───────────┼───────────────┼────────────────┤
       │iswalpha() │ Thread safety │ MT-Safe locale │
       ├───────────┼───────────────┼────────────────┤
       │iswblank() │ Thread safety │ MT-Safe locale │
       ├───────────┼───────────────┼────────────────┤
       │iswcntrl() │ Thread safety │ MT-Safe locale │
       ├───────────┼───────────────┼────────────────┤
       │iswdigit() │ Thread safety │ MT-Safe locale │
       ├───────────┼───────────────┼────────────────┤
       │iswgraph() │ Thread safety │ MT-Safe locale │
       ├───────────┼───────────────┼────────────────┤
       │iswlower() │ Thread safety │ MT-Safe locale │
       ├───────────┼───────────────┼────────────────┤
       │iswprint() │ Thread safety │ MT-Safe locale │
       ├───────────┼───────────────┼────────────────┤
       │iswpunct() │ Thread safety │ MT-Safe locale │
       ├──────────────────────────┼───────────────┼─────────────────────┤
       │iswspace() │ Thread safety │ MT-Safe locale │
       ├───────────┼───────────────┼────────────────┤
       │iswupper() │ Thread safety │ MT-Safe locale │
       ├────────────┼───────────────┼────────────────┤
       │iswxdigit() │ Thread safety │ MT-Safe locale │
       ├─────────────┼───────────────┼──────────────────────────────────┤
       │localeconv() │ Thread safety │ MT-Unsafe race:localeconv locale │
       ├──────────┼───────────────┼──────────────────────┤
       │login(),  │ Thread safety │ MT-Unsafe race:utent │
       │logout()  │               │ sig:ALRM timer       │
       ├──────────────┼───────────────┼────────────────────────────┤
       │makecontext() │ Thread safety │ MT-Safe race:ucp           │
       ├──────────────┼───────────────┼────────────────────────────┤
       │swapcontext() │ Thread safety │ MT-Safe race:oucp race:ucp │
       ├───────────┼───────────────┼──────────────────────────────┤
       │mallinfo() │ Thread safety │ MT-Unsafe init const:mallopt │
       ├──────────┼───────────────┼────────────────┤
       │mblen()   │ Thread safety │ MT-Unsafe race │
       ├──────────┼───────────────┼───────────────────────────┤
       │mbrlen()  │ Thread safety │ MT-Unsafe race:mbrlen/!ps │
       ├──────────┼───────────────┼────────────────────────────┤
       │mbrtowc() │ Thread safety │ MT-Unsafe race:mbrtowc/!ps │
       ├─────────────┼───────────────┼───────────────────────────────┤
       │mbsnrtowcs() │ Thread safety │ MT-Unsafe race:mbsnrtowcs/!ps │
       ├────────────┼───────────────┼──────────────────────────────┤
       │mbsrtowcs() │ Thread safety │ MT-Unsafe race:mbsrtowcs/!ps │
       ├──────────┼───────────────┼────────────────┤
       │mbtowc()  │ Thread safety │ MT-Unsafe race │
       ├─────────────────────────────┼───────────────┼───────────────────────┤
       │mcheck(), mcheck_pedantic(), │ Thread safety │ MT-Unsafe race:mcheck │
       │mcheck_check_all(), mprobe() │               │ const:malloc_hooks    │
       ├─────────────────────┼───────────────┼───────────┤
       │mtrace(), muntrace() │ Thread safety │ MT-Unsafe │
       ├──────────────┼───────────────┼────────────────┤
       │nl_langinfo() │ Thread safety │ MT-Safe locale │
       ├─────────────────────┼───────────────┼────────────────────────┤
       │forkpty(), openpty() │ Thread safety │ MT-Safe locale         │
       ├─────────────────────┼───────────────┼────────────────────────┤
       │login_tty()          │ Thread safety │ MT-Unsafe race:ttyname │
       ├──────────┼───────────────┼─────────────────────┤
       │perror()  │ Thread safety │ MT-Safe race:stderr │
       ├──────────────────┼───────────────┼─────────────────────────┤
       │posix_fallocate() │ Thread safety │ MT-Safe (but see NOTES) │
       ├─────────────────┼───────────────┼────────────────┤
       │valloc(),        │ Thread safety │ MT-Unsafe init │
       │pvalloc()        │               │                │
       ├────────────────────────┼───────────────┼────────────────┤
       │printf(), fprintf(),    │ Thread safety │ MT-Safe locale │
       │sprintf(), snprintf(),  │               │                │
       │vprintf(), vfprintf(),  │               │                │
       │vsprintf(), vsnprintf() │               │                │
       ├──────────┼───────────────┼───────────┤
       │profil()  │ Thread safety │ MT-Unsafe │
       ├──────────────────────┼───────────────┼────────────────┤
       │psignal(), psiginfo() │ Thread safety │ MT-Safe locale │
       ├────────────┼───────────────┼────────────────────────┤
       │ptsname()   │ Thread safety │ MT-Unsafe race:ptsname │
       ├──────────┼───────────────┼─────────────────────┤
       │putenv()  │ Thread safety │ MT-Unsafe const:env │
       ├───────────┼───────────────┼────────────────┤
       │putpwent() │ Thread safety │ MT-Safe locale │
       ├──────────┼───────────────┼──────────────────────┤
       │qecvt()   │ Thread safety │ MT-Unsafe race:qecvt │
       ├──────────┼───────────────┼──────────────────────┤
       │qfcvt()   │ Thread safety │ MT-Unsafe race:qfcvt │
       ├──────────┼───────────────┼──────────────────────┤
       │random_r(), srandom_r(),    │ Thread safety │ MT-Safe race:buf │
       │initstate_r(), setstate_r() │               │                  │
       ├────────────────────────────┼───────────────┼────────────────┤
       │rcmd(), rcmd_af()           │ Thread safety │ MT-Unsafe      │
       ├────────────────────────────┼───────────────┼────────────────┤
       │iruserok(), ruserok(),      │ Thread safety │ MT-Safe locale │
       │iruserok_af(), ruserok_af() │               │                │
       ├──────────┼───────────────┼──────────────────────────┤
       │readdir() │ Thread safety │ MT-Unsafe race:dirstream │
       ├─────────────────────┼───────────────┼───────────┤
       │re_comp(), re_exec() │ Thread safety │ MT-Unsafe │
       ├─────────────────────┼───────────────┼────────────────┤
       │regcomp(), regexec() │ Thread safety │ MT-Safe locale │
       ├─────────────────────┼───────────────┼────────────────┤
       │regerror()           │ Thread safety │ MT-Safe env    │
       ├───────────────────────────────────┼───────────────┼────────────────┤
       │res_ninit(),         res_nclose(), │ Thread safety │ MT-Safe locale │
       │res_nquery(),                      │               │                │
       │res_nsearch(), res_nquerydomain(), │               │                │
       │res_nsend()                        │               │                │
       ├────────────────────┼───────────────┼───────────┤
       │rexec(), rexec_af() │ Thread safety │ MT-Unsafe │
       ├──────────┼───────────────┼────────────────┤
       │rpmatch() │ Thread safety │ MT-Safe locale │
       ├──────────────────────────┼───────────────┼─────────────────────┤
       │alphasort(), versionsort() │ Thread safety │ MT-Safe locale │
       ├─────────────────────┼───────────────┼────────────────┤
       │scanf(), fscanf(),   │ Thread safety │ MT-Safe locale │
       │sscanf(), vscanf(),  │               │                │
       │vsscanf(), vfscanf() │               │                │
       ├────────────────────┼───────────────┼────────────────┤
       │setaliasent(), en‐  │ Thread safety │ MT-Safe locale │
       │daliasent(), getal‐ │               │                │
       │iasent_r(), getal‐  │               │                │
       │iasbyname_r()       │               │                │
       ├────────────────────┼───────────────┼────────────────┤
       │getaliasent(),      │ Thread safety │ MT-Unsafe      │
       │getaliasbyname()    │               │                │
       ├──────────────┼───────────────┼─────────────────────┤
       │setenv(), un‐ │ Thread safety │ MT-Unsafe const:env │
       │setenv()      │               │                     │
       ├────────────┼───────────────┼────────────────────────────┤
       │setlocale() │ Thread safety │ MT-Unsafe const:locale env │
       ├─────────────┼───────────────┼────────────────────────┤
       │setlogmask() │ Thread safety │ MT-Unsafe race:LogMask │
       ├─────────────────┼───────────────┼─────────────────────────┤
       │setnetgrent(),   │ Thread safety │ MT-Unsafe race:netgrent │
       │getnetgrent_r(), │               │ locale                  │
       │innetgr()        │               │                         │
       ├─────────────────┼───────────────┼─────────────────────────┤
       │endnetgrent()    │ Thread safety │ MT-Unsafe race:netgrent │
       ├─────────────────┼───────────────┼─────────────────────────┤
       │getnetgrent()    │ Thread safety │ MT-Unsafe race:netgrent │
       │                 │               │ race:netgrentbuf locale │
       ├─────────────────────────┼───────────────┼────────────────┤
       │shm_open(), shm_unlink() │ Thread safety │ MT-Safe locale │
       ├───────────────┼───────────────┼─────────────────────────┤
       │siginterrupt() │ Thread safety │ MT-Unsafe const:sigintr │
       ├──────────┼───────────────┼─────────────────────────────┤
       │sleep()   │ Thread safety │ MT-Unsafe sig:SIGCHLD/linux │
       ├──────────────────────┼───────────────┼─────────────────┤
       │va_arg()              │ Thread safety │ MT-Safe race:ap │
       ├─────────────────────────────┼───────────────┼─────────────────────┤
       │__fbufsize(), __fpending(),  │ Thread safety │ MT-Safe race:stream │
       │__fpurge(), __fsetlocking()  │               │                     │
       ├─────────────────────────────┼───────────────┼─────────────────────┤
       │strcasecmp(), strncasecmp() │ Thread safety │ MT-Safe locale │
       ├──────────┼───────────────┼────────────────┤
       │strcoll() │ Thread safety │ MT-Safe locale │
       ├──────────────────────────┼───────────────┼─────────────────────┤
       │strerror()         │ Thread safety │ MT-Unsafe race:strerror │
       ├────────────┼───────────────┼────────────────┤
       │strfmon()   │ Thread safety │ MT-Safe locale │
       ├────────────┼──────────────────────────────────┼────────────────┤
       │            │ Thread safety                    │ MT-Safe locale │
       │strfromd(), ├──────────────────────────────────┼────────────────┤
       │strfromf(), │ Asynchronous signal safety       │ AS-Unsafe heap │
       │strfroml()  ├──────────────────────────────────┼────────────────┤
       │            │ Asynchronous cancellation safety │ AC-Unsafe mem  │
       ├───────────┼───────────────┼────────────────────┤
       │strftime() │ Thread safety │ MT-Safe env locale │
       ├───────────┼───────────────┼────────────────────┤
       │strptime() │ Thread safety │ MT-Safe env locale │
       ├───────────────┼───────────────┼─────────────────────────────────┤
       │strsignal()    │ Thread safety │ MT-Unsafe race:strsignal locale │
       ├─────────────┼───────────────┼────────────────┤
       │strcasestr() │ Thread safety │ MT-Safe locale │
       ├──────────────────────────────┼───────────────┼────────────────┤
       │strtod(), strtof(), strtold() │ Thread safety │ MT-Safe locale │
       ├─────────────────────────┼───────────────┼────────────────┤
       │strtoimax(), strtoumax() │ Thread safety │ MT-Safe locale │
       ├───────────┼───────────────┼───────────────────────┤
       │strtok()   │ Thread safety │ MT-Unsafe race:strtok │
       ├──────────────────────────────┼───────────────┼────────────────┤
       │strtol(), strtoll(), strtoq() │ Thread safety │ MT-Safe locale │
       ├─────────────────────────────────┼───────────────┼────────────────┤
       │strtoul(), strtoull(), strtouq() │ Thread safety │ MT-Safe locale │
       ├──────────┼───────────────┼────────────────┤
       │strxfrm() │ Thread safety │ MT-Safe locale │
       ├──────────┼───────────────┼─────────────┤
       │sysconf() │ Thread safety │ MT-Safe env │
       ├──────────────────────┼───────────────┼────────────────────┤
       │syslog(), vsyslog()   │ Thread safety │ MT-Safe env locale │
       ├──────────┼───────────────┼─────────────┤
       │tempnam() │ Thread safety │ MT-Safe env │
       ├──────────────────────┼───────────────┼────────────────────┤
       │timelocal(), timegm() │ Thread safety │ MT-Safe env locale │
       ├───────────┼───────────────┼──────────────────────────┤
       │tmpnam()   │ Thread safety │ MT-Unsafe race:tmpnam/!s │
       ├─────────────┼───────────────┼────────────────┤
       │towlower()   │ Thread safety │ MT-Safe locale │
       ├─────────────┼───────────────┼────────────────┤
       │towupper()   │ Thread safety │ MT-Safe locale │
       ├────────────────────┼───────────────┼────────────────────┤
       │tsearch(), tfind(), │ Thread safety │ MT-Safe race:rootp │
       │tdelete()           │               │                    │
       ├────────────────────┼───────────────┼────────────────────┤
       │twalk()             │ Thread safety │ MT-Safe race:root  │
       ├────────────────────┼───────────────┼────────────────────┤
       │twalk_r()           │ Thread safety │ MT-Safe race:root  │
       ├────────────┼───────────────┼────────────────────────┤
       │ttyname()   │ Thread safety │ MT-Unsafe race:ttyname │
       ├──────────┼───────────────┼───────────┤
       │ttyslot() │ Thread safety │ MT-Unsafe │
       ├──────────┼───────────────┼────────────────────┤
       │tzset()   │ Thread safety │ MT-Safe env locale │
       ├─────────────────────┼───────────────┼───────────────────────┤
       │getc_unlocked(),     │ Thread safety │ MT-Safe race:stream   │
       │putc_unlocked(),     │               │                       │
       │clearerr_unlocked(), │               │                       │
       │fflush_unlocked(),   │               │                       │
       │fgetc_unlocked(),    │               │                       │
       │fputc_unlocked(),    │               │                       │
       │fread_unlocked(),    │               │                       │
       │fwrite_unlocked(),   │               │                       │
       │fgets_unlocked(),    │               │                       │
       │fputs_unlocked(),    │               │                       │
       │getwc_unlocked(),    │               │                       │
       │fgetwc_unlocked(),   │               │                       │
       │fputwc_unlocked(),   │               │                       │
       │putwc_unlocked(),    │               │                       │
       │fgetws_unlocked(),   │               │                       │
       │fputws_unlocked()    │               │                       │
       ├─────────────────────┼───────────────┼───────────────────────┤
       │getchar_unlocked(),  │ Thread safety │ MT-Unsafe race:stdin  │
       │getwchar_unlocked()  │               │                       │
       ├─────────────────────┼───────────────┼───────────────────────┤
       │putchar_unlocked(),  │ Thread safety │ MT-Unsafe race:stdout │
       │putwchar_unlocked()  │               │                       │
       ├───────────┼───────────────┼──────────────────────────┤
       │updwtmp(), │ Thread safety │ MT-Unsafe sig:ALRM timer │
       │logwtmp()  │               │                          │
       ├──────────┼───────────────┼────────────────────────────┤
       │wcrtomb() │ Thread safety │ MT-Unsafe race:wcrtomb/!ps │
       ├─────────────┼───────────────┼────────────────┤
       │wcscasecmp() │ Thread safety │ MT-Safe locale │
       ├──────────────┼───────────────┼────────────────┤
       │wcsncasecmp() │ Thread safety │ MT-Safe locale │
       ├─────────────┼───────────────┼───────────────────────────────┤
       │wcsnrtombs() │ Thread safety │ MT-Unsafe race:wcsnrtombs/!ps │
       ├────────────┼───────────────┼──────────────────────────────┤
       │wcsrtombs() │ Thread safety │ MT-Unsafe race:wcsrtombs/!ps │
       ├─────────────────────────┼───────────────┼────────────────┤
       │wcstoimax(), wcstoumax() │ Thread safety │ MT-Safe locale │
       ├───────────┼───────────────┼────────────────┤
       │wcswidth() │ Thread safety │ MT-Safe locale │
       ├──────────┼───────────────┼────────────────┤
       │wctomb()  │ Thread safety │ MT-Unsafe race │
       ├──────────┼───────────────┼────────────────┤
       │wctrans() │ Thread safety │ MT-Safe locale │
       ├──────────┼───────────────┼────────────────┤
       │wctype()  │ Thread safety │ MT-Safe locale │
       ├──────────┼───────────────┼────────────────┤
       │wcwidth() │ Thread safety │ MT-Safe locale │
       ├───────────┼───────────────┼────────────────────────────────┤
       │wordexp()  │ Thread safety │ MT-Unsafe race:utent const:env │
       │           │               │ env sig:ALRM timer locale      │
       ├─────────────────────────┼───────────────┼────────────────┤
       │wprintf(), fwprintf(),   │ Thread safety │ MT-Safe locale │
       │swprintf(), vwprintf(),  │               │                │
       │vfwprintf(), vswprintf() │               │                │
       └─────────────────────────┴───────────────┴────────────────┘
