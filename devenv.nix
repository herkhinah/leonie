{ pkgs, inputs, lib, ... }:
let
  fenix = inputs.fenix.packages.${pkgs.system}.stable;
in {
  # https://devenv.sh/pre-commit-hooks/
  pre-commit = {
    tools = {
      cargo = lib.mkForce fenix.cargo;
      rustfmt = lib.mkForce fenix.rustfmt;
      clippy = lib.mkForce fenix.clippy;
    };
    hooks = {
      clippy.enable = true;
      rustfmt.enable = true;
    };
  };
}
