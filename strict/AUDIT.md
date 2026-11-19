<!-- Modified for the source-focused edition, 12 November 2026. -->

# Verification boundary

This source distribution contains the Lean modules, the expected audit declarations, source hashes, a source-bound contract index, pinned dependency origins, offline checks, and a fresh replay runner.

It does not contain earlier execution logs, transcripts, review PDFs, nested review archives, compiled project objects, or repository history. Their omission is not a claim that this edition has been freshly verified.

The offline check establishes consistency of supplied files and metadata. It cannot establish that the theorem was accepted by Lean. A new replay must compile every module, verify dependency-output bindings, check the expected axiom reports, recheck all accepted objects, and confirm that the compiler/dependency inventory did not change during the run.

Standard Lean kernel assumptions are `propext`, `Classical.choice`, and `Quot.sound`. Source scans are deliberately narrow checks, not a complete Lean parser or a substitute for kernel checking.

See [VALIDATION.md](VALIDATION.md) for current status and [REPRODUCING.md](REPRODUCING.md) for the supported replay commands.
