"""Out-of-tree scheduling experiments on the proven register-cache body.

This is unverified experiment code. Native differential tests are mandatory;
any selected order must subsequently pass the Lean round checker.
"""
from pathlib import Path
import re
import json

HERE = Path(__file__).resolve().parent
OUT = HERE / 'out'
text = (HERE / 'row-cache.s').read_text()
start = text.index('\taddi a7, s2, 0', text.index('22:\n'))
middle = text.index('\taddi a7, s7, 0', start)
end = text.index('\taddi s0, s0, 16', middle)
rounds = [text[start:middle].splitlines(), text[middle:end].splitlines()]
assert len(rounds[0]) == len(rounds[1]) == 268


def resources(line):
    op, rest = line.strip().split(None, 1)
    operands = [x.strip() for x in rest.split(',')]
    if op == 'sd':
        base = operands[1].split('(')[1][:-1]
        return {operands[0], base}, {'mem:' + operands[1]}, False
    if op == 'ld':
        base = operands[1].split('(')[1][:-1]
        return {base, 'mem:' + operands[1]}, {operands[0]}, True
    reads = {r for operand in operands[1:] for r in re.findall(r'\b(?:a[0-7]|s(?:1[01]|[0-9])|t[0-6])\b', operand)}
    return reads, {operands[0]}, False


def schedule(lines, load_latency, width, window):
    rw = [resources(line) for line in lines]
    edges = [[] for _ in lines]
    predecessors = [[] for _ in lines]
    for j, (reads, writes, _) in enumerate(rw):
        for i in range(j):
            ri, wi, load = rw[i]
            if wi & reads or wi & writes or ri & writes:
                latency = (load_latency if load else 1) if wi & reads else 1
                edges[i].append((j, latency))
                predecessors[j].append((i, latency))
    critical = [1] * len(lines)
    for i in reversed(range(len(lines))):
        critical[i] = max([1] + [critical[j] + latency for j, latency in edges[i]])
    issued, order, cycle = {}, [], 0
    while len(order) < len(lines):
        first = next(i for i in range(len(lines)) if i not in issued)
        memory = False
        for _ in range(width):
            ready = [i for i in range(first, min(len(lines), first + window))
                     if i not in issued and all(p in issued and issued[p] + delay <= cycle for p, delay in predecessors[i])
                     and not (memory and lines[i].strip().split()[0] in ('ld', 'sd'))]
            if not ready:
                break
            i = max(ready, key=lambda i: (critical[i], -i))
            issued[i] = cycle
            order.append(i)
            memory |= lines[i].strip().split()[0] in ('ld', 'sd')
        cycle += 1
    return order, cycle


configs = [(2, 1, 16), (2, 2, 16), (3, 2, 16), (2, 2, 32), (3, 2, 32), (2, 2, 268), (3, 2, 268)]
orders = {}
names = ['asm_cache']
outputs = [text.replace('vg_keccak_f1600', 'candidate_asm_cache')]
for latency, width, window in configs:
    order, cycles = schedule(rounds[0], latency, width, window)
    other, _ = schedule(rounds[1], latency, width, window)
    assert order == other
    name = f'sched{latency}_{width}_{window}'
    names.append(name)
    orders[name] = order
    body = '\n'.join(rounds[0][i] for i in order) + '\n' + '\n'.join(rounds[1][i] for i in order) + '\n'
    outputs.append((text[:start] + body + text[end:]).replace('vg_keccak_f1600', 'candidate_' + name))
    print(name, cycles)
path = OUT / 'schedules.S'
path.write_text('.text\n' + '\n'.join('.globl candidate_' + n + '\n.type candidate_' + n + ', @function\n' + s for n, s in zip(names, outputs)))
with (OUT / 'asm-files.txt').open('a') as f:
    f.write(str(path) + '\n')
(OUT / 'orders.json').write_text(json.dumps(orders))
