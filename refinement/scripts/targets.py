"""The two Lean environments of the package, for census.py, controls.py and build-fold-bridge.py.

`main`: this package's lake workspace (the modules of Refinement/, Tree/, Balance/, Journey/ and
Gas/ over the gated model of the parent directory). `lake env lean` from the package directory.

`fold-bridge`: the modules of fold-bridge/, compiled in the workspace of ../circuits-lampe (Lampe
at its pinned fork, its stdlib, the extracted circuits and the circuits-lampe proof modules),
with the model and refinement modules they import compiled again from their sources into
build/fold-bridge/lib by build-fold-bridge.py. `lake -d <circuits-lampe> env lean`, with that
directory as LEAN_PATH (lake appends it after its own entries).
"""
import os
from dataclasses import dataclass, field
from pathlib import Path

PKG = Path(__file__).resolve().parent.parent
ROOT = PKG.parent
FB = PKG / 'fold-bridge'
FB_OUT = PKG / 'build' / 'fold-bridge' / 'lib'
FB_FLAGS = ['-M8192', '--tstack=65536', '-DElab.async=false', '-DmaxRecDepth=10000',
            '-DmaxHeartbeats=4000000']


def circuits_lampe():
    return Path(os.environ.get('CIRCUITS_LAMPE', ROOT / 'circuits-lampe')).resolve()


@dataclass
class Target:
    name: str
    cwd: Path
    flags: list
    groups: list
    census: str
    inventory: Path
    raw: Path
    controls: Path
    title: str
    lake_dir: Path = None
    env_extra: dict = field(default_factory=dict)

    def lean(self, *args):
        """argv and env to run `lean` with this target's flags on args, from self.cwd."""
        env = {**os.environ, **self.env_extra}
        lake = ['lake'] + (['-d', str(self.lake_dir)] if self.lake_dir else [])
        return lake + ['env', 'lean', *self.flags, *args], env


MAIN = Target('main', PKG, ['-M4096'], ['Refinement', 'Tree', 'Balance', 'Journey', 'Gas'],
              'Census.lean', PKG / 'statements' / 'INVENTORY.md', PKG / 'statements' / 'RAW.sha256',
              PKG / 'controls', 'Inventory of the theorems of the refinement package')


def fold_bridge():
    return Target('fold-bridge', FB, FB_FLAGS, ['FoldBridge'], 'Census.lean',
                  PKG / 'statements' / 'FOLD-BRIDGE.md', PKG / 'statements' / 'FOLD-BRIDGE.sha256',
                  FB / 'controls', 'Inventory of the theorems of the fold bridge (fold-bridge/)',
                  lake_dir=circuits_lampe(), env_extra={'LEAN_PATH': str(FB_OUT)})


def target(name):
    return MAIN if name == 'main' else fold_bridge()
