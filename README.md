# Geode

Geode is a hash-based argument of knowledge for batches of unmodified FIPS 204 ML-DSA-87
signatures. One certificate attests, for a range of already validated blocks, knowledge of
canonical ML-DSA-87 signatures on exactly the recorded messages under the recorded keys. At
N = 65,536 signatures the unique-decoding certificate is 8,315,630 bytes, 126.89 bytes per
signature, against 4,627 bytes for one raw signature; the Johnson-regime certificate is
104.09 bytes per signature.

This repository holds the code, test vectors, transcripts and ledger scripts behind the paper
*Archive Certificates for ML-DSA-87 Authorizations from an Exact Bounded Relation*
(Yacine Alloul, preprint, version 1, 2026). It lets a reader rebuild the prover and verifier and
rerun the paper's commands for the hidden-u certificates (authentication profile QLYAUTH7), in both
parameter families: unique decoding (U) and Johnson (J).

## What Geode is not

These limits are stated in the paper and apply to everything here:

- **No throughput gain.** Certificates archive blocks that were already validated. Fresh blocks
  keep native signature verification, and a certificate does not reduce fresh-block traffic.
- **Verification is slower than native.** Checking a certificate costs several times the native
  verification of the same signatures. The prover is slow: the first prover took about 52 minutes
  at N = 65,536 and the faster one about 11 to 33 minutes, partly disk-bound.
- **The quantum bound is conditional.** A quantum-random-oracle extraction bound is stated for the
  unique-decoding family only, conditional on cited Reed–Solomon proximity theorems and the
  hypotheses listed in the paper. It is a failure probability at a stated budget, not a work
  factor. The Johnson family and the public-u profile carry a classical bound only.
- **No independent review yet.** Implementation correspondence is tested, not proved; the cited
  theorems were not re-checked; the recent short proofs were checked only by the author's internal
  review; no independent expert has yet reviewed the proof against the code. Until then
  certificate-only bootstrap must stay disabled.
- **Laboratory profiles.** The hidden-u profiles are laboratory profiles over a laboratory chain
  with synthetic headers. No zero knowledge, data availability or NIST category 5 claim is made for
  the certificate.

## Layout

| Path | Contents |
|---|---|
| `aggregate/r3-cert/` | The Rust crate: prover, verifier, acceptance suites, attacks, measurements (`src/`), Cargo files and lockfile, the vendored and patched `p3-challenger` 0.8.0 (`vendor/`, see its `R3-CERT-PATCH.txt`), and every transcript the paper cites (`transcripts/`). |
| `aggregate/r7-check/` | Fiat–Shamir codec test vectors; the crate includes `expected.txt` at build time. |
| `aggregate/hint-check/` | `hint.c`, an independent C check of the interval form of UseHint (FIPS 204 Algorithms 36 to 40), and its output. |
| `aggregate/r6-check/`, `aggregate/r8-check/` | The public-u ledgers and their outputs. |
| `aggregate/r10-security/` | `ledger10.py`, the hidden-u security ledger, its output `ledger10.txt`, and the round registries it reads. |
| `aggregate/r10-jobs/` | The job scripts that produced the large-N transcripts in a Linux container. |
| `aggregate/cert-speed/` | Job scripts, container recipe and export script of the faster-prover runs and reruns; `verifier-unchanged.py`. |
| `paper/scripts/`, `paper/data/` | `bcgm_registered.py` and `registry_bytes.py` and their outputs. |
| `PROVENANCE.md`, `provenance/` | Map from each laboratory commit cited by the paper to its tag here, with SHA-256 sums. |

The paper cites laboratory commits by hash. Each one is a tag here: `lab-4cc5598` is the tree of
lab commit `4cc5598`, and so on. `PROVENANCE.md` gives the full table, what was left out and what
was changed (comments and printed paths only; no code).

## Toolchain

| Tool | Version used |
|---|---|
| Rust | 1.96.0 (`rust-toolchain.toml` pins it; the crate builds with `--locked`) |
| Plonky3 crates | `=0.8.0`, one file of `p3-challenger` patched and vendored |
| Python | 3.14 (standard library only) for the ledgers |
| C compiler | any C99 compiler, for `hint.c` |
| GNU time, procps, sysstat | for the container job scripts (Linux) |

Measurements in the paper were made on Linux (Intel Xeon 6975P-C and AMD EPYC 9655P hosts, 24 vCPU
and 24 GB containers) and on an Apple M3 Pro. Certificates are deterministic: the same statement
gives the same certificate bytes on any host. Binary digests recorded in the transcripts are
host-specific and are not part of the protocol.

## Build

```sh
git checkout lab-4cc5598        # the tree of the paper's main commands; main holds the faster prover
cd aggregate/r3-cert
cargo build --release --locked; B=target/release/r3-cert
cargo build --release --locked --features lab-hooks --target-dir target-lab
L=target-lab/release/r3-cert    # test hooks: acceptance suites and prover comparisons only
```

The default build has no test hooks; use it for every measurement and verification. The crate has
no `cargo test` unit tests: its self checks and acceptance suites are subcommands, below.

## Reproducing the paper

Certificates are written to `$R3_OUT` (default: the current directory). Large ranges need disk
space: at N = 65,536 the arrays spill to `H9_SPILL_DIR` and the prover reads and writes several
hundred GiB.

| Paper result | Command (in `aggregate/r3-cert`, tag given) | Transcript |
|---|---|---|
| Self checks | `$B selftest; $B h9self; $B r10self` | `transcripts/selftest.txt` |
| Acceptance suites, 223/223 per family (Table of tests) | `$L h9tests 128` and `H9_FAMILY=ud $L h9tests 128` | `transcripts/r10-tests128.txt`, `transcripts/r10-gates.txt` |
| Bytes, phases and memory at N = 2,048, family J | `H9_FAMILY=johnson $B h9 2048` | `transcripts/r10-first.txt`, `transcripts/r10-dftsmall.txt` |
| Round registry and honest run, family U | `H9_FAMILY=ud $B h9registry 2048 run` | `transcripts/r10-registry-*.txt` |
| Chain ranges at N = 4,096 and 16,384 | `H9_FAMILY=johnson $B h9chain 4096` (and `ud`, and 16384) | `transcripts/r10-m4096.txt`, `r10-m16384.txt` |
| 104.09 B/signature, family J, N = 65,536 (`lab-a02cb7a`) | `H9_SPILL_DIR=/tmp/spill H9_SPILL_MIN=67108864 H9_FAMILY=johnson $B h9chain 65536` | `transcripts/r10-m65536.txt` |
| 126.89 B/signature, family U, N = 65,536 (`lab-68cc4e1`) | the same with `H9_FAMILY=ud` | `transcripts/r10-m65536ud.txt` |
| Verifier-side attacks, 49/49 | `$B h9chainattacks 65536 <certificate>` | `transcripts/r10-attacks65536.txt` |
| Certificate digests | `shasum -a 256` of the files above | `transcripts/r10-final.txt` lines 100 to 108 |
| Public-u profile QLYAUTH7 | `$B chainmeasure v7; $B soundness v7` | `transcripts/r7-*`, `transcripts/r8-*` |

The faster prover (Section "A faster prover with the same certificates") is `lab-2aced2d`; its
transcripts are complete at `lab-bc4788b` under `transcripts/cert-speed/`. The identity check builds
the default binaries of both provers and compares certificate digests:

```sh
# in aggregate/r3-cert; BASE, B: default builds of lab-0e7a1c9 and lab-2aced2d
export H9_FAMILY=ud H9_SPILL_DIR=/tmp/spill H9_SPILL_MIN=67108864 H9_SPILL_SEQ=1
R3_OUT=out/base $BASE h9chain 16384; R3_OUT=out/new $B h9chain 16384
shasum -a 256 out/base/h9chain-cert-16384-fff9130e.bin out/new/h9chain-cert-16384-fff9130e.bin
R3_OUT=out/new $B h9chain 65536     # sha256 c9fbf852..., as recorded
C=out/new/h9chain-cert-65536-fff91310.bin
$BASE h9chainverify 65536 $C        # verifier of the first prover
$B h9chainattacks 65536 $C          # 49/49
cd ../..; python3 aggregate/cert-speed/verifier-unchanged.py lab-0e7a1c9 lab-2aced2d
```

The reruns at N = 65,536 (Section "Reproduction at 65,536 signatures") built a container from
`aggregate/cert-speed/export.sh <empty dir> lab-bc4788b lab-0e7a1c9` and ran
`aggregate/cert-speed/jobs/rerun65536.sh` and `rerun65536t.sh`; their transcripts are under
`transcripts/rerun-65536/` (`lab-8c866e5`) and `transcripts/rerun-65536-amd/` (`lab-3d9332b`).

Ledgers and checks, from the repository root on `main`:

```sh
cc -O2 -o hint aggregate/hint-check/hint.c && ./hint      # = aggregate/hint-check/result.txt
python3 aggregate/r10-security/ledger10.py                # = aggregate/r10-security/ledger10.txt
python3 paper/scripts/bcgm_registered.py                  # = paper/data/bcgm-registered.txt
python3 paper/scripts/registry_bytes.py                   # = paper/data/registry-bytes.txt
bash aggregate/r6-check/ledger.sh                         # = aggregate/r6-check/ledger.txt
bash aggregate/r8-check/check.sh                          # = aggregate/r8-check/check.txt
```

`ledger10.txt` differs from a fresh run only in the line that prints the registry directory.

The paper also reports runs inside a node and sustained proving under full blocks. Their code and
evidence are not part of this release.

## License

Geode is source-available under the Business Source License 1.1 (`LICENSE`). Anyone may read,
build, modify and run it for non-production use, such as research, reproduction of the paper's
results, evaluation and testing. Production use requires a commercial licence from the author.
On 2030-11-03 the code converts to the GNU General Public License v2.0 or later. Geode is the
subject of a pending patent application (`NOTICE`).

The vendored `p3-challenger` 0.8.0 under `aggregate/r3-cert/vendor/` keeps its own licence
(MIT OR Apache-2.0, text in its directory).
