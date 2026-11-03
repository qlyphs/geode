# Dockerfile: the cert-speed service (prover speed work on the
# hidden-u certificate). The image holds two r3-cert source trees exported from commits by
# export.sh: the baseline (r10 head 0e7a1c9) and the commit under test. entry.sh builds both
# into the volume at start-up and then idles; jobs run over a remote shell.
FROM rust:1.96.0-trixie@sha256:58fe97504a0e4cbba5d85599619a589923d3e779472a6fb0840d58d1c4ba99d7
RUN apt-get update && apt-get install -y --no-install-recommends time procps ca-certificates sysstat && rm -rf /var/lib/apt/lists/*
COPY src /src
ENV DATA_DIR=/data
CMD ["/src/cert-speed/entry.sh"]
