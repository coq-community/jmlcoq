# JMLCoq

[![Travis][travis-shield]][travis-link]

[travis-shield]: https://travis-ci.com/palmskog/jmlcoq.svg?branch=master
[travis-link]: https://travis-ci.com/palmskog/jmlcoq/builds




A formalization of the Java-based JML specification language,
along with a verified runtime assertion checker for JML.

## Meta

- Author(s):
  - Hermann Lehner (initial)
  - David Pichardie (initial)
  - Andreas Kägi (initial)
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.9 or later
- Additional dependencies: none
- Coq namespace: `JML`
- Related publication(s):
  - [A Formalization of JML in the Coq Proof System](https://www.research-collection.ethz.ch/handle/20.500.11850/68882) doi:[https://doi.org/10.3929/ethz-a-006903145](https://doi.org/https://doi.org/10.3929/ethz-a-006903145)

## Building instructions

``` shell
git clone https://github.com/palmskog/jmlcoq
cd jmlcoq
make   # or make -j <number-of-cores-on-your-machine>
```

## Documentation

More information about the formalization can be found on the
[project website](http://jmlcoq.info).
