FROM coqorg/coq:8.11-ocaml-4.10-flambda

COPY _CoqProject .
COPY CpdtTactics.v .
COPY Dockerfile .
COPY SyntaxRuntime.v .
COPY OperationalSemantics.v .
COPY Typing.v .
COPY MetaTheoryBase.v .
COPY MetaTheoryLocalConfluence.v .
COPY MetaTheoryTyping.v .
COPY MetaTheory.v .
COPY Makefile .
COPY Makefile.conf .
COPY Maps.v .
COPY NMaps.v .

CMD make
