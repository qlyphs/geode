# Dockerfile: the cert-prover service (round 10, large-N hidden-u
# certificates). The image holds the r3-cert sources (exported from one commit by export.sh) and
# a compiler; entry.sh builds the release binary at start-up into the volume (a hosted image
# build stops after about 60 min) and then idles, so measurement jobs run over a remote shell.
FROM rust:1.96.0-trixie@sha256:58fe97504a0e4cbba5d85599619a589923d3e779472a6fb0840d58d1c4ba99d7
RUN apt-get update && apt-get install -y --no-install-recommends time procps ca-certificates && rm -rf /var/lib/apt/lists/*
COPY src /src
ENV DATA_DIR=/data
CMD ["/src/r10-jobs/entry.sh"]
