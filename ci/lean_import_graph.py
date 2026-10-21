"""Lean module visibility, including distinct ordinary and meta imports.

The rules follow Lake/CLI/Shake.lean's addTransitiveImps: ordinary imports
expose public ordinary declarations; public meta exports propagate along both
kinds of public edge. `import all` additionally exposes private dependencies.
"""

Import = tuple[str, bool, bool, bool]  # module, public, meta, all


class VisibilityGraph:
    def __init__(self):
        self.passed: dict[str, frozenset[str]] = {}
        self.meta_passed: dict[str, frozenset[str]] = {}
        self.read_cache: dict[bool, dict[str, frozenset[str]]] = {False: {}, True: {}}

    def imports(self, mod: str) -> list[Import]:
        raise NotImplementedError

    def reuse_passes(self, mod: str) -> frozenset[str] | None:
        return None

    def reuse_meta_exports(self, mod: str) -> frozenset[str] | None:
        return None

    def passes(self, mod: str) -> frozenset[str]:
        """The module itself and its PUBLIC ORDINARY closure."""
        stack, active = [(mod, False)], set()
        while stack:
            m, ready = stack.pop()
            if m in self.passed:
                continue
            reused = self.reuse_passes(m)
            if reused is not None:
                self.passed[m] = reused
                continue
            on = [i for i, public, meta, _ in self.imports(m) if public and not meta]
            if ready:
                self.passed[m] = frozenset({m}).union(*(self.passed[i] for i in on))
                active.remove(m)
            else:
                if m in active:
                    raise ValueError(f"cyclic public import graph at {m}")
                active.add(m)
                stack.append((m, True))
                stack.extend((i, False) for i in on if i not in self.passed)
        return self.passed[mod]

    def meta_exports(self, mod: str) -> frozenset[str]:
        """Public meta capabilities supplied by an ORDINARY import of mod."""
        stack, active = [(mod, False)], set()
        while stack:
            m, ready = stack.pop()
            if m in self.meta_passed:
                continue
            reused = self.reuse_meta_exports(m)
            if reused is not None:
                self.meta_passed[m] = reused
                continue
            on = [(i, meta) for i, public, meta, _ in self.imports(m) if public]
            if ready:
                result = set().union(*(self.meta_passed[i] for i, _ in on))
                for i, meta in on:
                    if meta:
                        result.update(self.passes(i))
                self.meta_passed[m] = frozenset(result)
                active.remove(m)
            else:
                if m in active:
                    raise ValueError(f"cyclic public import graph at {m}")
                active.add(m)
                stack.append((m, True))
                stack.extend((i, False) for i, _ in on if i not in self.meta_passed)
        return self.meta_passed[mod]

    def meta_passes(self, mod: str) -> frozenset[str]:
        """What importing mod AS META supplies to elaboration-time code."""
        return self.passes(mod) | self.meta_exports(mod)

    def reads(self, mod: str, meta: bool = False, active: set[str] | None = None) -> frozenset[str]:
        table = self.read_cache[meta]
        if mod in table:
            return table[mod]
        active = set() if active is None else active
        if mod in active:
            raise ValueError(f"cyclic import-all graph at {mod}")
        active.add(mod)
        result = set()
        for i, public, is_meta, all_ in self.imports(mod):
            if meta:
                result.update(self.meta_passes(i) if is_meta else self.meta_exports(i))
            elif not is_meta:
                result.update(self.passes(i))
            if all_ and not public and (meta or not is_meta):
                result.update(self.reads(i, meta, active))
        active.remove(mod)
        table[mod] = frozenset(result)
        return table[mod]
