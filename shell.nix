{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  # inputsFrom = with pkgs; [  ];
  buildInputs = [ pkgs.ocaml pkgs.dune (import ../nix/mlcuddidl/default.nix ) ] ++
                (with pkgs.ocamlPackages;
                  [ findlib menhir core ppx_jane ppx_deriving ]);
}

