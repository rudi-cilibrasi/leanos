#!/usr/bin/env python3
"""Run real consumers through manifest preflight, stopping before compilation.

Injected queries test failure propagation. Real malformed manifests test named
validation errors. The continuation sentinel does not stand in for a build.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
OPERATIONS = ('packaged-images', 'page-plans', 'disassemblies',
              'extended-state-policies', 'entry-policies')


def main():
    with tempfile.TemporaryDirectory(prefix='leanos-build-manifest-') as directory:
        root = Path(directory)
        scripts = root / 'scripts'
        scripts.mkdir()
        for name in ('build-image.sh', 'check-expectation-templates.sh', 'scenario-manifest.py'):
            shutil.copy2(ROOT / 'scripts' / name, scripts / name)
        query = scripts / 'scenario-manifest.py'
        real_query = query.read_bytes()
        manifest = json.loads((ROOT / 'scripts/scenario-manifest.json').read_text())
        for path in (ROOT / 'scripts').glob('direct-port-sites*.tsv'):
            shutil.copy2(path, scripts / path.name)
        # A custom matrix avoids invoking unrelated generation before preflight.
        (root / 'matrix.tsv').write_text('fixture\treturn\tfail\t30\ti\te\tl\tf\t1\tr\tpr\n')
        sentinel = '#!/bin/bash\nprintf "continuation\\n" >> reached\nexit 97\n'
        for name in ('toolchain-profile.py', 'generate-oracle.sh'):
            (scripts / name).write_text(sentinel)
            (scripts / name).chmod(0o755)
        (scripts / 'toolchain-profile.py').write_text(
            '#!/bin/bash\nif [[ " $* " == *" --format tsv "* ]]; then\n'
            '  printf "gcc-reference\\tsupported\\tfixture\\tfixture\\tfixture\\thash\\tgcc\\tfixture\\n"\n'
            '  exit 0\nfi\nprintf "continuation\\n" >> reached\nexit 97\n')

        def run(script, operation='', mode=''):
            (root / 'reached').unlink(missing_ok=True)
            return subprocess.run(['bash', 'scripts/' + script], cwd=root,
                                  env=dict(os.environ, LEANOS_EVIDENCE_MATRIX='matrix.tsv',
                                           LEANOS_SOURCE_REVISION='1' * 40,
                                           LEANOS_VERSION='0.1.0', TEST_OPERATION=operation,
                                           TEST_MODE=mode), text=True, capture_output=True)

        def rejected(result, diagnostic):
            assert result.returncode not in (0, 97), result
            assert not (root / 'reached').exists(), result
            assert diagnostic in result.stderr, result

        # Preserve the real query's valid rows, then inject a producer failure.
        (scripts / 'scenario-manifest.json').write_text(json.dumps(manifest))
        outputs = {}
        for operation in OPERATIONS:
            outputs[operation] = subprocess.check_output([str(query), operation], cwd=root, text=True)
        query.write_text('''#!/usr/bin/env python3
import json, os, sys
from pathlib import Path
outputs = json.loads(Path('outputs.json').read_text())
operation = sys.argv[1]
if operation == os.environ['TEST_OPERATION']:
    mode = os.environ['TEST_MODE']
    if mode == 'partial':
        print(outputs[operation].splitlines()[0], flush=True)
    if mode != 'empty':
        print('injected manifest query failure', file=sys.stderr)
        sys.exit(7)
else:
    print(outputs[operation], end='')
''')
        outputs['expectations'] = 'scenario\tboot\tscripts/fixture.transcript\n'
        (root / 'outputs.json').write_text(json.dumps(outputs))
        for script, operations in (('build-image.sh', OPERATIONS),
                                   ('check-expectation-templates.sh', ('expectations',))):
            result = run(script)
            assert result.returncode == 97 and (root / 'reached').exists(), result
            for operation in operations:
                for mode in ('failure', 'partial', 'empty'):
                    result = run(script, operation, mode)
                    rejected(result, 'no ' if mode == 'empty' else 'injected manifest query failure')

        query.write_bytes(real_query)
        mutations = (
            ('packaged_images', {}, 'packaged_images'),
            ('page_plan_stub_extras', ['invalid'], 'page-plan stub extra'),
            ('disassemblies', [], 'disassemblies'),
            ('extended_state_policies', [], 'extended_state_policies'),
            ('entry_policies', [], 'entry_policies'),
        )
        for key, value, diagnostic in mutations:
            changed = json.loads(json.dumps(manifest))
            changed['build'][key] = value
            (scripts / 'scenario-manifest.json').write_text(json.dumps(changed))
            rejected(run('build-image.sh'), diagnostic)
        (scripts / 'scenario-manifest.json').write_text(json.dumps(manifest))
        result = run('build-image.sh')
        assert result.returncode == 97 and (root / 'reached').exists(), result
    print('Build and expectation consumers reject failed/partial/empty queries before continuation')


if __name__ == '__main__':
    main()
