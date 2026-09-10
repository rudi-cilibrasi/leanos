"""Validate complete parallel hosted evidence for every CI trigger."""


def validate(workflow):
    jobs = workflow['jobs']
    lean, hosted = jobs['lean'], jobs['hosted-boundary']
    for job in (lean, hosted):
        if 'if' in job or job.get('needs') or job.get('continue-on-error'):
            raise ValueError('proof and hosted jobs must independently run on every trigger')
    proof = next(s for s in lean['steps'] if s.get('run') == './scripts/check.sh')
    if proof.get('env', {}).get('LEANOS_SKIP_HOSTED_BOUNDARY_REPLAY') != '1':
        raise ValueError('aggregate check must delegate hosted replay on every trigger')
    if proof.get('if') or proof.get('continue-on-error'):
        raise ValueError('aggregate check cannot be conditional or optional')
    commands = [
        'lake build',
        'lake build leanos-boot-plan',
        'lake build leanos-vtd-plan',
        './scripts/test-hosted-boundary-harness-scan.sh',
        './scripts/check-hosted-generated-boundaries.sh ordinary',
        './scripts/check-hosted-generated-boundaries.sh sanitized',
        './scripts/check-hosted-sanitizer-negatives.sh',
    ]
    replay = next(s for s in hosted['steps'] if s.get('name') == 'Replay hosted generated boundaries')
    if replay.get('run', '').splitlines() != commands:
        raise ValueError('hosted replay must retain all build, ordinary, sanitizer and negative checks')
    if replay.get('if') or replay.get('continue-on-error'):
        raise ValueError('hosted replay cannot be conditional or optional')
    for name in ('leanos-oracle-${{ github.sha }}', 'hosted-sanitizers-${{ github.sha }}'):
        producers = [(job_id, step) for job_id, job in jobs.items()
                     for step in job.get('steps', [])
                     if step.get('uses', '').startswith('actions/upload-artifact@')
                     and step.get('with', {}).get('name') == name]
        if len(producers) != 1 or producers[0][0] != 'hosted-boundary':
            raise ValueError('hosted artifacts require exactly one producer on every trigger')
        step = producers[0][1]
        if step.get('if') != 'always()' or step['with'].get('if-no-files-found') != 'error':
            raise ValueError('hosted artifacts must retain diagnostics and reject missing evidence')
    if 'hosted-boundary' not in jobs['premerge-admission']['needs']:
        raise ValueError('premerge admission must still depend on hosted evidence')

