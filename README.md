# Total

A playground for working with Total Languages.

## Goal

Write verified compilers from Surface Syntax to RISC-V Assembly (specifically,
`rv64i`) for each of the simple total languages listed below.

## Approach

K.I.S.S.

In regards to the languages, they should have just enough features to make them
interesting but not more (Numbers and Booleans, but not Strings, Products, Sums,
etc.)

Verifications should focus on being clear and explicit rather than being the
shortest or most elegant.

## Nice To Haves (Secondary Goals)

* Simple optimizations (basic inlining, 0CFA)
* Compilation pipeline language
* Separate compilation/modules system
* Shared RISC-V assembly that all languages compile to
* Possibly a shared IR that all languages compile to
* Verified runtime systems like GC
* Better Currying algorithm

# Languages

## Simply-Typed Lambda Calculus (STLC)

**Status:** In Progress

The STLC with Numbers and Booleans and without `fix`.

## Elementary Strong Functional Programming (ESFP)

**Status:** Not Started

Turner & Telford's ESFP.

## Fair Reactive

**Status:** Not Started

Andrew Cave's Fair Reactive language based on LTL and the μ-Calculus.

## Stretch: HDub

**Status:** Not Started

A version of Fair Reactive turned into a HDL.  (May do this *instead of* a
straight Fair Reactive.)