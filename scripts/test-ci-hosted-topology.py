#!/usr/bin/env python3
"""Require hosted evidence on every CI trigger, with one artifact producer."""

from copy import deepcopy
from pathlib import Path

from ci_hosted_topology import validate
from workflow_yaml import load_workflow


workflow = load_workflow(Path(__file__).resolve().parents[1] / '.github/workflows/ci.yml')
validate(workflow)


def rejects(change):
    mutated = deepcopy(workflow)
    change(mutated['jobs'])
    try:
        validate(mutated)
    except ValueError:
        return
    raise AssertionError('unsafe hosted CI topology accepted')


rejects(lambda jobs: jobs['hosted-boundary'].update({'if': "github.event_name == 'pull_request'"}))
rejects(lambda jobs: jobs['hosted-boundary'].update({'needs': ['lean']}))
rejects(lambda jobs: jobs['hosted-boundary'].update({'continue-on-error': True}))
rejects(lambda jobs: next(s for s in jobs['lean']['steps'] if s.get('run') == './scripts/check.sh')
        ['env'].update({'LEANOS_SKIP_HOSTED_BOUNDARY_REPLAY': '0'}))
rejects(lambda jobs: next(s for s in jobs['hosted-boundary']['steps']
                         if s.get('name') == 'Replay hosted generated boundaries')
        .update({'run': 'lake build'}))
rejects(lambda jobs: next(s for s in jobs['hosted-boundary']['steps']
                         if s.get('name') == 'Replay hosted generated boundaries')
        .update({'continue-on-error': True}))
rejects(lambda jobs: jobs['lean']['steps'].append(deepcopy(next(
    s for s in jobs['hosted-boundary']['steps']
    if s.get('with', {}).get('name') == 'leanos-oracle-${{ github.sha }}'))))
rejects(lambda jobs: next(s for s in jobs['hosted-boundary']['steps']
                         if s.get('with', {}).get('name') == 'hosted-sanitizers-${{ github.sha }}')
        ['with'].update({'if-no-files-found': 'warn'}))
rejects(lambda jobs: jobs['premerge-admission']['needs'].remove('hosted-boundary'))
print('Hosted CI topology passed; nine unsafe mutations rejected')
