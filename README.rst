================
isabelle_parser
================

.. image:: https://github.com/christiankissig/python-isabelle-parser/actions/workflows/ci.yml/badge.svg?branch=master
   :target: https://github.com/christiankissig/python-isabelle-parser/actions/workflows/ci.yml
   :alt: CI/CD status

.. image:: https://img.shields.io/badge/python-3.10%2B-blue.svg
   :target: https://www.python.org/downloads/
   :alt: Python 3.10+

.. image:: https://img.shields.io/badge/license-MIT-green.svg
   :target: https://github.com/christiankissig/python-isabelle-parser/blob/master/LICENSE
   :alt: License: MIT

A parser for `Isabelle/Isar <https://isabelle.in.tum.de/>`_ theory (``.thy``)
artifacts, implemented in pure Python on top of `Lark <https://lark-parser.org/>`_
using an Earley grammar.

It turns the outer syntax of a theory file — the theory header, document
markup, specifications (``definition``, ``datatype``, ``fun``, ``locale``,
``class``, …), Isar proofs and FFI/ML commands — into a Lark parse tree that you
can walk programmatically.

Status
======

Work in progress. The grammar covers a large and growing share of the outer
syntax found in the `Archive of Formal Proofs <https://www.isa-afp.org/>`_, but
it is not yet complete: inner-syntax terms with exotic notation, some proof
methods, and a few rarely-used commands are still rejected. Treat a successful
parse as authoritative and a failure as "not yet supported" rather than "invalid
Isabelle".

Metrics
=======

Parser coverage and performance against the latest `Archive of Formal Proofs
<https://www.isa-afp.org/>`_ release, refreshed weekly by the ``metrics``
workflow (and on demand via *Run workflow*):

.. METRICS:START

.. list-table::
   :header-rows: 1
   :widths: 45 55

   * - Metric
     - Value
   * - AFP snapshot
     - afp-2026-06-19
   * - Files sampled
     - 500
   * - Parse coverage
     - 32.4% (162 parsed)
   * - Timeouts (> 15s)
     - 23.4% (117)
   * - Throughput
     - 0.77 files/s · 0.023 MB/s (×4 workers)
   * - Median parse time (parsed files)
     - 2.422 s
   * - Measured
     - 2026-06-22 06:09 UTC

*Coverage is the share of a seeded random sample of AFP theory files that parse within the timeout; a whole file counts as failed if any statement fails. Updated weekly by the metrics workflow.*

.. METRICS:END

Requirements
============

* Python >= 3.10
* `lark <https://pypi.org/project/lark/>`_

Installation
============

From a clone of the repository:

.. code-block:: bash

   pip install .

For a development checkout (tests, linters):

.. code-block:: bash

   pip install -e ".[dev]"

Command-line usage
==================

The CLI parses a file or a literal string and prints the resulting tree:

.. code-block:: bash

   # parse a theory file
   python -m isabelle_parser.cli -f path/to/Theory.thy

   # parse a literal string
   python -m isabelle_parser.cli "theory T imports Main begin end"

Options:

``-f``, ``--file``
   Interpret the input argument as a filename rather than a literal string.

``-t``, ``--timeout SECONDS``
   Abort the parse after ``SECONDS`` and report a failure instead of hanging.
   The Earley chart can grow super-linearly on large or highly ambiguous files,
   so this is a useful guard when parsing a whole corpus.

The command exits non-zero if parsing fails.

Library usage
=============

.. code-block:: python

   from isabelle_parser import parse, load_parser, ParsingError

   source = "theory T imports Main begin\nlemma \"x = x\" by simp\nend"

   try:
       tree = parse(source)
       print(tree.pretty())
   except ParsingError as error:
       print(f"parsing failed: {error}")

``parse(input_text, parser=None, timeout=None)``
   Parse ``input_text`` and return a Lark ``Tree``. If ``parser`` is omitted a
   default parser is built for the ``start`` rule. ``timeout`` (seconds) bounds
   the parse and raises ``ParsingError`` if exceeded; it relies on ``SIGALRM``
   and therefore applies only on the main thread of a Unix process (it is
   silently skipped elsewhere).

``load_parser(start="start")``
   Build and return the underlying Lark parser, optionally starting from a
   specific grammar rule. Reuse a single instance when parsing many files —
   building the parser is the expensive part.

``ParsingError``
   Raised for invalid input and on timeout. Lark may also raise its own
   ``lark.exceptions.UnexpectedInput`` subclasses for structurally invalid input.

Development
===========

.. code-block:: bash

   pytest            # run the test suite
   ruff check .      # lint
   ruff format .     # format
   isort .           # import ordering

The grammar lives in ``isabelle_parser/thy_grammar.lark``.

License
=======

MIT. See the ``LICENSE`` file.
