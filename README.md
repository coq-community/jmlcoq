<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# JMLCoq

[![Docker CI][docker-action-shield]][docker-action-link]
[![Nix CI][nix-action-shield]][nix-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/coq-community/jmlcoq/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/coq-community/jmlcoq/actions/workflows/docker-action.yml

[nix-action-shield]: https://github.com/coq-community/jmlcoq/actions/workflows/nix-action.yml/badge.svg?branch=master
[nix-action-link]: https://github.com/coq-community/jmlcoq/actions/workflows/nix-action.yml

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



A Coq formalization of the syntax and semantics of the
Java-targeted JML specification language, along with a
verified runtime assertion checker for JML.

## Meta

- Author(s):
  - Hermann Lehner (initial)
  - David Pichardie (initial)
  - Andreas Kägi (initial)
- Coq-community maintainer(s):
  - Karl Palmskog ([**@palmskog**](https://github.com/palmskog))
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.10 or later
- Additional dependencies: none
- Coq namespace: `JML`
- Related publication(s):
  - [A formal definition of JML in Coq and its application to runtime assertion checking](https://www.research-collection.ethz.ch/handle/20.500.11850/44276) doi:[10.3929/ethz-a-006680049](https://doi.org/10.3929/ethz-a-006680049)
  - [A Formalization of JML in the Coq Proof System](https://www.research-collection.ethz.ch/handle/20.500.11850/68882) doi:[10.3929/ethz-a-006903145](https://doi.org/10.3929/ethz-a-006903145)

## Building and installation instructions

The easiest way to install the latest released version of JMLCoq
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-jmlcoq
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/jmlcoq.git
cd jmlcoq
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Documentation

More information about the formalization can be found on the
[project website](http://jmlcoq.info).
