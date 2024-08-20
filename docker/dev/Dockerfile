FROM debian:bookworm-slim

ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update -y && \
  apt install -y --no-install-recommends \
    wget \
    curl \
    build-essential \
    sudo \
    gpg


    
# setup dev user
RUN groupadd -g 1000 dev \
&& useradd dev -u 1000 -g 1000 -s /bin/bash
RUN mkdir -p /workspace \
&& chown -R dev:dev /workspace
RUN mkdir -p /home/dev \
&& chown -R dev:dev /home/dev
RUN usermod -aG sudo dev
RUN echo "dev ALL=(ALL) NOPASSWD: ALL" >> /etc/sudoers

USER dev

RUN cd ~ && wget --no-check-certificate https://raw.githubusercontent.com/leanprover-community/mathlib4/master/scripts/install_debian.sh && bash install_debian.sh
