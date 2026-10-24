---
name: Ticket
about: A ticket whose Done-when lines are checkable
---

## What is wrong / what is wanted

(evidence: links, commands run, numbers)

## Done when

Every line is one of four forms. A line that is not one of them is not a Done-when line.

1. COMMAND: `<command>` prints or exits `<value>`.
2. MEASURE: `<metric>` on a named real workload, measured once, with the number the line requires and the raw output posted.
3. TEST: `<named test>` fails on the base commit and passes on the head.
4. SEARCH: `git grep -n <pattern> -- <paths>` prints nothing, or exactly these lines.

A "research" line is a COMMAND line.

## Not in this ticket

Each excluded item with its own ticket number.
