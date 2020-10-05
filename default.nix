with import (builtins.fetchTarball {
  url = https://github.com/nixos/nixpkgs/archive/1085c056376041af71e8f1cf72c1ed4a4db01dc6.tar.gz;
  sha256 = "17sh68825jhjfpn1q02ni8xifrgaszz494irx096f0mmi2k2lkqp";
}) {};

stdenv.mkDerivation rec {
  name = "PolyGen";
  doCheck = true;
  src = nix-gitignore.gitignoreSource [] ./.;
  buildInputs = (with pkgs.ocaml-ng.ocamlPackages_4_07; [
    ocaml
    findlib
    menhir
    zarith
    glpk
  ]) ++ [ coq_8_7 ];
  buildPhase = ''
    make vplsetup
    make
    make extract
    make ocaml
  '';
  checkPhase = ''
    ocaml/test
  '';
  installPhase = ''
    mkdir -p "$out/bin"
    cp ocaml/test "$out/bin/test"
  '';
}
