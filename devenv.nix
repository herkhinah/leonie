{ pkgs, inputs, lib, ... }:
let
  fenix = inputs.fenix.packages.${pkgs.system};
  toolchain = fenix.stable;
in 
{
  packages = [ toolchain.toolchain fenix.rust-analyzer ];

  enterShell = ''
    vscode-settings
  '';

  scripts.vscode-settings.exec = ''
    mkdir -p .vscode
    touch -a .vscode/settings.json

    cat <<EOF > .vscode/settings.json
    {
      "rust-analyzer.cargo.sysroot": "${toolchain.toolchain}",
      "rust-analyzer.server.path": "${fenix.rust-analyzer}/bin/rust-analyzer"
    }
    EOF
  '';

  pre-commit = {
    tools = {
      cargo = lib.mkForce toolchain.cargo;
      rustfmt = lib.mkForce toolchain.rustfmt;
      clippy = lib.mkForce toolchain.clippy;
    };
    hooks = {
      clippy.enable = true;
      rustfmt.enable = true;
    };
  };
}
