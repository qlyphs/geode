# Provenance

Every result in the paper comes from a commit of a private laboratory repository. Its history is
not published. Instead, each cited commit is reproduced here as one commit of this repository,
tagged `lab-<hash>`, whose tree holds the files of that lab commit that are needed to rebuild and
rerun the certificate, filtered as described below. The tags form one linear history in the order
of the lab commits. `git checkout lab-4cc5598` gives the tree from which the paper's main commands
run; `main` holds the last snapshot plus this documentation and the paper's ledger scripts.

## Cited commits and their public location

| Lab commit | Date | Role in the paper | Public location | Files | Changed for publication |
|---|---|---|---|---|---|
| `40a46c1b46a3c6ea3a055ed0d2f5f4abafdd7ad0` | 2026-10-23 | Public-u profile QLYAUTH7: code of the public-u transcripts | tag `lab-40a46c1` | 105 | 6 |
| `3d38ed3370da5c298380f1b8936293c69b88818a` | 2026-10-23 | Public-u profile: round-8 test code (attack8, route8) | tag `lab-3d38ed3` | 114 | 6 |
| `3e8291be07f06af991754909fc2c5a88208af22d` | 2026-10-24 | Hidden-u: first server transcripts | tag `lab-3e8291b` | 136 | 14 |
| `89bd14de58239a3005b1c4a04bdc8ee644c47bbc` | 2026-10-24 | Hidden-u: first suites, Keccak-path comparison, sizes and memory at N <= 2048 | tag `lab-89bd14d` | 140 | 18 |
| `3e5e9a433f2a4887a730deef1b5d34a58555b79d` | 2026-10-24 | Hidden-u: round registries, runs at N = 4,096 and 16,384 | tag `lab-3e5e9a4` | 144 | 21 |
| `a02cb7ae0a84de038013cb639928247ad4382ef5` | 2026-10-24 | Hidden-u: Johnson run at N = 65,536 | tag `lab-a02cb7a` | 170 | 24 |
| `68cc4e16e850688b62f99dda6d6638dc681cb826` | 2026-10-24 | Hidden-u: unique-decoding run at N = 65,536 | tag `lab-68cc4e1` | 174 | 28 |
| `fea3f280527a258f3d091524adc85df1d9a233f7` | 2026-10-24 | Hidden-u: final acceptance suites | tag `lab-fea3f28` | 166 | 23 |
| `4cc5598e09359b2144d6202665c0b7c5bea8ea78` | 2026-10-24 | Hidden-u: registries from the default build, certificate digests; the paper's main commands | tag `lab-4cc5598` | 221 | 48 |
| `0e7a1c922526fc641e9a861ea5d75438975d4224` | 2026-10-24 | Hidden-u: results commit of the large-N branch; baseline of the faster prover | tag `lab-0e7a1c9` | 232 | 48 |
| `1e5432b2abc2adfaae923ed530f4faeab1a8326b` | 2026-10-25 | Faster prover: prover code identical to 2aced2d | tag `lab-1e5432b` | 267 | 50 |
| `2aced2ddda69618356d5d300cca1fd92904e5db3` | 2026-10-25 | Faster prover: the optimised prover | tag `lab-2aced2d` | 271 | 50 |
| `1dc8500300ce58936647e195d15605cf1c1ec37e` | 2026-10-25 | Faster prover: comparison transcripts | tag `lab-1dc8500` | 290 | 50 |
| `bc4788bc5d328141a07d780d0a223ca1d9fae200` | 2026-10-25 | Faster prover: corrected results commit (transcripts as of this commit); source of the reruns | tag `lab-bc4788b` | 290 | 50 |
| `8c866e5e244c18d0b053b0720eae23bbe03bf31b` | 2026-10-26 | Rerun at N = 65,536, host D | tag `lab-8c866e5` | 294 | 51 |
| `3d9332b3b2fd6fa73e3f41ff08f9696076d06256` | 2026-10-26 | Reruns at N = 65,536, hosts E and F | tag `lab-3d9332b` | 310 | 51 |
| `cbc32e49a1f66f968876f72999f72178630322ee` | 2026-10-24 | Security branch: ledger10.py, ledger10.txt and the round registries | tag `lab-cbc32e4`, directory `aggregate/r10-security/` | 12 | 1 |

Each tag's file list with SHA-256 sums is in `provenance/lab-<hash>.sha256` (sums of the published
files; check a checkout with `sha256sum -c provenance/lab-<hash>.sha256` from the repository root).
For the security tag the list covers `aggregate/r10-security/` only; the rest of that tree is the
`lab-3d9332b` snapshot.

## Cited commits not included in this release

| Lab commit | Cited for | Status |
|---|---|---|
| `0c1b420` | in-node runs (Section "In a node") | not included in this release |
| `846f976` | in-node runs | not included in this release |
| `070e766` | in-node runs | not included in this release |
| `d7b2a9b` | in-node results | not included in this release |
| `2833ab4` | sustained runs (Section "Keeping up with full blocks") | not included in this release |
| `cd4f871` | sustained runs, corrected results file | not included in this release |
| `60b99e1` | prover build of the sustained runs | not included in this release |
| `bfde9ff` | later single-worker campaign | not included in this release |
| `c6a0b62` | revision of the security document | not included: it changes only a document that this release does not contain (see below) |

## What was left out of every snapshot

- `aggregate/r3-cert/PROTOCOL.md`, `RESULTS*.md` and `RERUN-65536-ud.md`: laboratory notes that
  record hosting-provider accounts, costs, local paths and references to unpublished review
  material. The paper states their results; the transcripts they cite are included.
- `aggregate/r10-security/SECURITY-hidden-u.md` and `SECURITY-qlyauth7-repair.md`: the security
  argument is published as Section 7 and Appendix C of the paper.
- `aggregate/r10-security/hidden_ledger_r9.py` (superseded draft) and `__pycache__/`.
- Every other directory of the lab repository: they are not needed to rebuild or rerun the certificate.

## What was changed

Changes keep every file's line count, so line numbers cited elsewhere still hold. No change touches
code: only comments, file names, paths printed in transcripts, and comments of the job scripts.
The certificate bytes do not depend on any of them.

- The laboratory job directory, whose name named the hosting service, is published as `aggregate/r10-jobs/`; paths inside
  its scripts follow. Comments of `aggregate/r10-jobs/` and `aggregate/cert-speed/` no longer name
  the hosting service or its project.
- Five comment lines of `aggregate/r3-cert/src/fs7.rs` and `src/main.rs` cite an unpublished design
  note; they now say "the round-7 design notes" or "the inline reference program".
- Transcripts recorded on the development machine printed a long local temporary directory; it is
  shown as `/tmp/`.
- File names of 19 memory-sample transcripts in `transcripts/r10-mem/` ended in a carriage return
  before `.txt`; it was removed.
- `transcripts/rerun-65536/host.txt`: the name of an unrelated queued job is replaced.
- `aggregate/r10-security/ledger10.txt`: the absolute registry path is shown relative to the
  repository root.

Every changed file, with the SHA-256 of the lab file and of the published file, is listed in
`provenance/changed.tsv`.

## Certificate digests

Certificates are not committed: they are deterministic, and their SHA-256 digests are recorded in
the transcripts (for example `aggregate/r3-cert/transcripts/r10-final.txt` lines 100 to 108, and
`c9fbf852d0ac6cdaa7fcde08184e5036a5f13a6e28f68e6b9269d6a72e34f20a` for the unique-decoding
certificate at N = 65,536).

## Other files on `main`

`paper/scripts/bcgm_registered.py` and `paper/scripts/registry_bytes.py` are the paper's scripts,
changed only to read `aggregate/r10-security/` in this repository instead of a lab checkout; their
outputs in `paper/data/` are byte-identical to the files the paper cites.
