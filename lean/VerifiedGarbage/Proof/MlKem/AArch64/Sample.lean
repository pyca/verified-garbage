import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.AArch64.Stream.Squeeze
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd2
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Impl.MlKem.AArch64.Top
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.MlKem.AArch64.Sample

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall`. -/
section

/-!
# ML-KEM on AArch64: calling the Keccak functions

Each call of the verified `vg_keccak_absorb`, `vg_keccak_pad` and
`vg_keccak_squeeze`, from its proof (with `WP.callF`: they save `x30` in a
frame): what it needs of the state it is called from, and what holds when it
returns (`Kept`: only the regions it may write and its frame's 16 bytes below
the stack pointer change, and the callee-saved registers but `x30` are kept).
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64
open VG.Spec.Sha3 (Repr stateAt bytesAt absorb pad squeezeFrom rates)

/-- `s'` differs from `s` only in memory within `rs` and in registers that
are not callee-saved (or are `x30`). -/
structure Kept (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem
  vcs : ∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

/-- The 16 bytes below the stack pointer, where a callee saves `x30`. -/
abbrev stk (s : State) : Region := ⟨s.sp - 16, 16⟩

theorem absorb_fdepth : Impl.Sha3.AArch64.Stream.absorb.aarch64Depth = 1 := by decide +kernel
theorem pad_fdepth : Impl.Sha3.AArch64.Stream.pad.aarch64Depth = 1 := by decide +kernel
theorem squeeze_fdepth : Impl.Sha3.AArch64.Stream.squeeze.aarch64Depth = 1 := by decide +kernel

theorem frame3 {a b c : Region} {m m' : Mem} (h : Frame ([a, b] ++ [c]) m m') : Frame [a, b, c] m m' := h

theorem frame4 {a b c d : Region} {m m' : Mem} (h : Frame ([a, b, c] ++ [d]) m m') :
    Frame [a, b, c, d] m m' := h

theorem gpr_entry (s : State) {r : Reg} (h : r ∉ linkRegs := by decide) : s.callEntry.gpr r = s.gpr r :=
  State.callEntry_gpr s h

/-- `vg_keccak_absorb(st, rate, pos, dt, len, sc)`. -/
theorem absorb_callWith (v : Proof.Sha3.AArch64.Permutation) {s : State} {st dt sc : Addr} {rate pos len : Nat}
    (h0 : s.gpr .x0 = st) (h1 : (s.gpr .x1).toNat = rate) (h2 : (s.gpr .x2).toNat = pos)
    (h3 : s.gpr .x3 = dt) (h4 : (s.gpr .x4).toNat = len) (h5 : s.gpr .x5 = sc)
    (hr : rate ∈ rates) (hp : pos < rate)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨sc, 640⟩) (d₂ : Region.Disjoint ⟨dt, len⟩ ⟨st, 200⟩)
    (d₃ : Region.Disjoint ⟨dt, len⟩ ⟨sc, 640⟩) (hsp : 16 ≤ s.sp.toNat)
    (k₁ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨st, 200⟩) (k₂ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨dt, len⟩)
    (k₃ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨sc, 640⟩)
    (hc : Covers [⟨dt, len⟩, ⟨st, 200⟩, ⟨sc, 640⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨sc, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.MlKem.AArch64.Kept [⟨st, 200⟩, ⟨sc, 640⟩, below s.sp 16] s s' →
      (∀ msg, Repr s.mem st rate msg → pos = msg.length % rate →
        Repr s'.mem st rate (msg ++ bytesAt s.mem dt len)) →
      (s'.gpr .x0).toNat = (pos + len) % rate → Q s') :
    WP isa (.call ("vg_keccak_absorb_scratch" ++ v.callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith v.callee)) s Q := by
  have c0 : s.callEntry.gpr .x0 = st := (VG.Proof.MlKem.AArch64.gpr_entry s).trans h0
  have c1 : (s.callEntry.gpr .x1).toNat = rate := by rw [VG.Proof.MlKem.AArch64.gpr_entry s]; exact h1
  have c2 : (s.callEntry.gpr .x2).toNat = pos := by rw [VG.Proof.MlKem.AArch64.gpr_entry s]; exact h2
  have c3 : s.callEntry.gpr .x3 = dt := (VG.Proof.MlKem.AArch64.gpr_entry s).trans h3
  have c4 : (s.callEntry.gpr .x4).toNat = len := by rw [VG.Proof.MlKem.AArch64.gpr_entry s]; exact h4
  have c5 : s.callEntry.gpr .x5 = sc := (VG.Proof.MlKem.AArch64.gpr_entry s).trans h5
  refine WP.callFV (k := Proof.Sha3.absorbAArch64) (Proof.Sha3.AArch64.Stream.Absorb.absorb_correct v)
    (rd := [⟨dt, len⟩]) (wr := [⟨st, 200⟩, ⟨sc, 640⟩]) ?_ hc hw ?_ (by rw [v.absorb_depth]; decide)
  · simp only [Proof.Sha3.absorbAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, c0, c1, c2, c3, c4, c5]
    exact ⟨trivial, trivial, d₁, d₂, d₃, hsp, k₁, k₂, k₃, hr, hp⟩
  · intro s' hrd hwr hsp' hf hcs hv hpost
    rw [v.absorb_depth, Nat.mul_one] at hf
    simp only [Proof.Sha3.absorbAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, c3, c4] at hpost
    exact hQ s' ⟨hcs, hsp', hrd, hwr, VG.Proof.MlKem.AArch64.frame3 hf, hv⟩ hpost.1 hpost.2

theorem absorb_call {s : State} {st dt sc : Addr} {rate pos len : Nat}
    (h0 : s.gpr .x0 = st) (h1 : (s.gpr .x1).toNat = rate) (h2 : (s.gpr .x2).toNat = pos)
    (h3 : s.gpr .x3 = dt) (h4 : (s.gpr .x4).toNat = len) (h5 : s.gpr .x5 = sc)
    (hr : rate ∈ rates) (hp : pos < rate)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨sc, 640⟩) (d₂ : Region.Disjoint ⟨dt, len⟩ ⟨st, 200⟩)
    (d₃ : Region.Disjoint ⟨dt, len⟩ ⟨sc, 640⟩) (hsp : 16 ≤ s.sp.toNat)
    (k₁ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨st, 200⟩) (k₂ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨dt, len⟩)
    (k₃ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨sc, 640⟩)
    (hc : Covers [⟨dt, len⟩, ⟨st, 200⟩, ⟨sc, 640⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨sc, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.MlKem.AArch64.Kept [⟨st, 200⟩, ⟨sc, 640⟩, below s.sp 16] s s' →
      (∀ msg, Repr s.mem st rate msg → pos = msg.length % rate →
        Repr s'.mem st rate (msg ++ bytesAt s.mem dt len)) →
      (s'.gpr .x0).toNat = (pos + len) % rate → Q s') :
    WP isa (.call "vg_keccak_absorb_scratch" Impl.Sha3.AArch64.Stream.absorb) s Q :=
  VG.Proof.MlKem.AArch64.absorb_callWith .scalar h0 h1 h2 h3 h4 h5 hr hp d₁ d₂ d₃ hsp k₁ k₂ k₃ hc hw hQ

/-- `vg_keccak_pad(st, rate, pos, suffix, sc)`. -/
theorem pad_callWith (v : Proof.Sha3.AArch64.Permutation) {s : State} {st sc : Addr} {rate pos : Nat}
    (h0 : s.gpr .x0 = st) (h1 : (s.gpr .x1).toNat = rate) (h2 : (s.gpr .x2).toNat = pos)
    (h4 : s.gpr .x4 = sc) (hr : rate ∈ rates) (hp : pos < rate)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨sc, 640⟩) (hsp : 16 ≤ s.sp.toNat)
    (k₁ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨st, 200⟩) (k₃ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨sc, 640⟩)
    (hc : Covers [⟨st, 200⟩, ⟨sc, 640⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨sc, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.MlKem.AArch64.Kept [⟨st, 200⟩, ⟨sc, 640⟩, below s.sp 16] s s' →
      (∀ msg, Repr s.mem st rate msg → pos = msg.length % rate →
        stateAt s'.mem st = absorb rate (pad rate ((s.gpr .x3).setWidth 8) msg)) → Q s') :
    WP isa (.call ("vg_keccak_pad_scratch" ++ v.callee.suffix) (Impl.Sha3.AArch64.Stream.padWith v.callee)) s Q := by
  have c0 : s.callEntry.gpr .x0 = st := (VG.Proof.MlKem.AArch64.gpr_entry s).trans h0
  have c1 : (s.callEntry.gpr .x1).toNat = rate := by rw [VG.Proof.MlKem.AArch64.gpr_entry s]; exact h1
  have c2 : (s.callEntry.gpr .x2).toNat = pos := by rw [VG.Proof.MlKem.AArch64.gpr_entry s]; exact h2
  have c3 : s.callEntry.gpr .x3 = s.gpr .x3 := VG.Proof.MlKem.AArch64.gpr_entry s
  have c4 : s.callEntry.gpr .x4 = sc := (VG.Proof.MlKem.AArch64.gpr_entry s).trans h4
  refine WP.callFV (k := Proof.Sha3.padAArch64) (Proof.Sha3.AArch64.Stream.Pad.pad_correct v)
    (rd := []) (wr := [⟨st, 200⟩, ⟨sc, 640⟩]) ?_ hc hw ?_ (by rw [v.pad_depth]; decide)
  · simp only [Proof.Sha3.padAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, c0, c1, c2, c4]
    exact ⟨trivial, trivial, d₁, hsp, k₁, k₃, hr, hp⟩
  · intro s' hrd hwr hsp' hf hcs hv hpost
    rw [v.pad_depth, Nat.mul_one] at hf
    simp only [Proof.Sha3.padAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, c3] at hpost
    exact hQ s' ⟨hcs, hsp', hrd, hwr, VG.Proof.MlKem.AArch64.frame3 hf, hv⟩ hpost

theorem pad_call {s : State} {st sc : Addr} {rate pos : Nat}
    (h0 : s.gpr .x0 = st) (h1 : (s.gpr .x1).toNat = rate) (h2 : (s.gpr .x2).toNat = pos)
    (h4 : s.gpr .x4 = sc) (hr : rate ∈ rates) (hp : pos < rate)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨sc, 640⟩) (hsp : 16 ≤ s.sp.toNat)
    (k₁ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨st, 200⟩) (k₃ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨sc, 640⟩)
    (hc : Covers [⟨st, 200⟩, ⟨sc, 640⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨sc, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.MlKem.AArch64.Kept [⟨st, 200⟩, ⟨sc, 640⟩, below s.sp 16] s s' →
      (∀ msg, Repr s.mem st rate msg → pos = msg.length % rate →
        stateAt s'.mem st = absorb rate (pad rate ((s.gpr .x3).setWidth 8) msg)) → Q s') :
    WP isa (.call "vg_keccak_pad_scratch" Impl.Sha3.AArch64.Stream.pad) s Q :=
  VG.Proof.MlKem.AArch64.pad_callWith .scalar h0 h1 h2 h4 hr hp d₁ hsp k₁ k₃ hc hw hQ

/-- `vg_keccak_squeeze(st, rate, pos, out, len, sc)`. -/
theorem squeeze_callWith (v : Proof.Sha3.AArch64.Permutation) {s : State} {st out sc : Addr} {rate pos len : Nat}
    (h0 : s.gpr .x0 = st) (h1 : (s.gpr .x1).toNat = rate) (h2 : (s.gpr .x2).toNat = pos)
    (h3 : s.gpr .x3 = out) (h4 : (s.gpr .x4).toNat = len) (h5 : s.gpr .x5 = sc)
    (hr : rate ∈ rates) (hp : pos ≤ rate)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨out, len⟩) (d₂ : Region.Disjoint ⟨st, 200⟩ ⟨sc, 640⟩)
    (d₃ : Region.Disjoint ⟨out, len⟩ ⟨sc, 640⟩) (hsp : 16 ≤ s.sp.toNat)
    (k₁ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨st, 200⟩) (k₂ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨out, len⟩)
    (k₃ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨sc, 640⟩)
    (hc : Covers [⟨st, 200⟩, ⟨out, len⟩, ⟨sc, 640⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨out, len⟩, ⟨sc, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.MlKem.AArch64.Kept [⟨st, 200⟩, ⟨out, len⟩, ⟨sc, 640⟩, below s.sp 16] s s' →
      bytesAt s'.mem out len = squeezeFrom rate (stateAt s.mem st) pos len →
      (s'.gpr .x0).toNat ≤ rate →
      (∀ d, squeezeFrom rate (stateAt s'.mem st) (s'.gpr .x0).toNat d =
        squeezeFrom rate (stateAt s.mem st) (pos + len) d) → Q s') :
    WP isa (.call ("vg_keccak_squeeze_scratch" ++ v.callee.suffix) (Impl.Sha3.AArch64.Stream.squeezeWith v.callee)) s Q := by
  have c0 : s.callEntry.gpr .x0 = st := (VG.Proof.MlKem.AArch64.gpr_entry s).trans h0
  have c1 : (s.callEntry.gpr .x1).toNat = rate := by rw [VG.Proof.MlKem.AArch64.gpr_entry s]; exact h1
  have c2 : (s.callEntry.gpr .x2).toNat = pos := by rw [VG.Proof.MlKem.AArch64.gpr_entry s]; exact h2
  have c3 : s.callEntry.gpr .x3 = out := (VG.Proof.MlKem.AArch64.gpr_entry s).trans h3
  have c4 : (s.callEntry.gpr .x4).toNat = len := by rw [VG.Proof.MlKem.AArch64.gpr_entry s]; exact h4
  have c5 : s.callEntry.gpr .x5 = sc := (VG.Proof.MlKem.AArch64.gpr_entry s).trans h5
  refine WP.callFV (k := Proof.Sha3.squeezeAArch64) (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_correct v)
    (rd := []) (wr := [⟨st, 200⟩, ⟨out, len⟩, ⟨sc, 640⟩]) ?_ hc hw ?_
    (by rw [v.squeeze_depth]; decide)
  · simp only [Proof.Sha3.squeezeAArch64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, c0, c1, c2, c3, c4, c5]
    exact ⟨trivial, trivial, d₁, d₂, d₃, hsp, k₁, k₂, k₃, hr, hp⟩
  · intro s' hrd hwr hsp' hf hcs hv hpost
    rw [v.squeeze_depth, Nat.mul_one] at hf
    simp only [Proof.Sha3.squeezeAArch64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0, c1, c2, c3, c4] at hpost
    exact hQ s' ⟨hcs, hsp', hrd, hwr, VG.Proof.MlKem.AArch64.frame4 hf, hv⟩ hpost.1 hpost.2.1 hpost.2.2

theorem squeeze_call {s : State} {st out sc : Addr} {rate pos len : Nat}
    (h0 : s.gpr .x0 = st) (h1 : (s.gpr .x1).toNat = rate) (h2 : (s.gpr .x2).toNat = pos)
    (h3 : s.gpr .x3 = out) (h4 : (s.gpr .x4).toNat = len) (h5 : s.gpr .x5 = sc)
    (hr : rate ∈ rates) (hp : pos ≤ rate)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨out, len⟩) (d₂ : Region.Disjoint ⟨st, 200⟩ ⟨sc, 640⟩)
    (d₃ : Region.Disjoint ⟨out, len⟩ ⟨sc, 640⟩) (hsp : 16 ≤ s.sp.toNat)
    (k₁ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨st, 200⟩) (k₂ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨out, len⟩)
    (k₃ : (VG.Proof.MlKem.AArch64.stk s).Disjoint ⟨sc, 640⟩)
    (hc : Covers [⟨st, 200⟩, ⟨out, len⟩, ⟨sc, 640⟩] (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨out, len⟩, ⟨sc, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.MlKem.AArch64.Kept [⟨st, 200⟩, ⟨out, len⟩, ⟨sc, 640⟩, below s.sp 16] s s' →
      bytesAt s'.mem out len = squeezeFrom rate (stateAt s.mem st) pos len →
      (s'.gpr .x0).toNat ≤ rate →
      (∀ d, squeezeFrom rate (stateAt s'.mem st) (s'.gpr .x0).toNat d =
        squeezeFrom rate (stateAt s.mem st) (pos + len) d) → Q s') :
    WP isa (.call "vg_keccak_squeeze_scratch" Impl.Sha3.AArch64.Stream.squeeze) s Q :=
  VG.Proof.MlKem.AArch64.squeeze_callWith .scalar h0 h1 h2 h3 h4 h5 hr hp d₁ d₂ d₃ hsp k₁ k₂ k₃ hc hw hQ

end VG.Proof.MlKem.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.HashProof`. -/
section

/-!
# ML-KEM-768 on AArch64: the hash routine

`hash` (`Impl/MlKem/AArch64/Top.lean`) computes the sponge of the
concatenation of its input pieces, and writes consecutive output to its output
pieces (`hash_ok`): from the all-zero state (`repr_nil`), each `absorb`
continues the message from the position the previous one returned, the
padding, and each `squeeze` continues the output. It changes only the Keccak
state and working space, the outputs, the 16 bytes below the stack pointer,
and registers that are not callee-saved (or `x30`).
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.Sha3 (Repr stateAt bytesAt absorb pad squeezeFrom rates)

/-! ## What changes -/

theorem Kept.refl (rs : List Region) (s : State) : VG.Proof.MlKem.AArch64.Kept rs s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ _ => rfl⟩

theorem Kept.trans {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.MlKem.AArch64.Kept rs s₁ s₂) (h₂ : VG.Proof.MlKem.AArch64.Kept rs s₂ s₃) :
    VG.Proof.MlKem.AArch64.Kept rs s₁ s₃ :=
  ⟨fun r hr h => by rw [h₂.cs r hr h, h₁.cs r hr h], by rw [h₂.sp, h₁.sp], by rw [h₂.rd, h₁.rd],
    by rw [h₂.wr, h₁.wr], h₁.frame.trans h₂.frame, fun r hr => (h₂.vcs r hr).trans (h₁.vcs r hr)⟩

theorem Kept.sub {rs rs' : List Region} {s s' : State} (h : VG.Proof.MlKem.AArch64.Kept rs s s')
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', Region.Sub r r') : VG.Proof.MlKem.AArch64.Kept rs' s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame.sub hs, h.vcs⟩

theorem Kept.mono {rs rs' : List Region} {s s' : State} (h : VG.Proof.MlKem.AArch64.Kept rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    VG.Proof.MlKem.AArch64.Kept rs' s s' :=
  h.sub fun r hr => ⟨r, hs r hr, fun _ h => h⟩

/-- A block that writes no callee-saved register nor memory. -/
theorem Kept.of_keep {rs : List Region} {regs : List Reg} {s s' : State} (hk : Keep regs s s')
    (hm : s'.mem = s.mem) (hr : ∀ r ∈ preserved, r ∉ regs) : VG.Proof.MlKem.AArch64.Kept rs s s' :=
  ⟨fun r hp _ => hk.gpr r (hr r hp), hk.sp, hk.rd, hk.wr, by rw [hm]; exact Frame.refl _ _, hk.vcs⟩

theorem pres_not {r : Reg} (h : r ∈ preserved) :
    r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 ∧ r ≠ .x5 ∧ r ≠ .x9 := by
  revert r h; decide

/-! ## Addresses -/

theorem wp_ptrTo {d b : Reg} {off : Nat} (hd : d ≠ b) (ho : off < 65536) {is : List Instr} {s : State}
    {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr b + BitVec.ofNat 64 off → WP isa (.block is) s' Q) :
    WP isa (.block (ptrTo d b off ++ is)) s Q := by
  unfold ptrTo
  split
  · exact wp_addImm ‹_› k
  · refine wp_movz fun s₁ h₁ e₁ => wp_add fun s₂ h₂ e₂ => k s₂ ((h₁.trans h₂).mono (by simp)) ?_
    rw [e₂, h₁.get b (by simpa using hd.symm), e₁]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [toNat_imm, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega

/-- `ptrTo` at the end of a block. -/
theorem wp_ptrTo' {d b : Reg} {off : Nat} (hd : d ≠ b) (ho : off < 65536) {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr b + BitVec.ofNat 64 off → Q s') :
    WP isa (.block (ptrTo d b off)) s Q := by
  rw [← List.append_nil (ptrTo d b off)]
  exact VG.Proof.MlKem.AArch64.wp_ptrTo hd ho fun s' h e => wp_nil (k s' h e)

theorem wp_pos (first : Bool) {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [.x2] s s' → (s'.gpr .x2).toNat = (if first then 0 else (s.gpr .x0).toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block ((if first then [.movz .x .x2 0 0] else [mov .x2 .x0]) ++ is)) s Q := by
  cases first
  · exact wp_mov fun s' h e => k s' h (by rw [e]; rfl)
  · exact wp_movz fun s' h e => k s' h (by rw [e]; rfl)

theorem imm16 {v : Nat} (h : v < 65536) : ((BitVec.ofNat 16 v).setWidth 64).toNat = v := by
  rw [toNat_imm, BitVec.toNat_ofNat]; omega

/-! ## The setting -/

/-- A piece at `s`. -/
abbrev preg (s : State) (p : Piece) : Region := ⟨s.gpr p.base + BitVec.ofNat 64 p.off, p.len⟩

/-- Its bytes at `s`. -/
abbrev pbytes (s : State) (p : Piece) : List Byte := bytesAt s.mem (s.gpr p.base + BitVec.ofNat 64 p.off) p.len

/-- The Keccak state and working space at `sc + st` and `sc + wk`. -/
structure HSetup (sc : Reg) (st wk rate : Nat) (s₀ : State) : Prop where
  hsc : sc ∈ preserved ∧ sc ≠ .x30
  hst : st < 65536
  hwk : wk < 65536
  hrate : rate ∈ rates
  d : Region.Disjoint ⟨s₀.gpr sc + BitVec.ofNat 64 st, 200⟩ ⟨s₀.gpr sc + BitVec.ofNat 64 wk, 640⟩
  sp16 : 16 ≤ s₀.sp.toNat
  kst : (VG.Proof.MlKem.AArch64.stk s₀).Disjoint ⟨s₀.gpr sc + BitVec.ofNat 64 st, 200⟩
  kwk : (VG.Proof.MlKem.AArch64.stk s₀).Disjoint ⟨s₀.gpr sc + BitVec.ofNat 64 wk, 640⟩
  cov : Covers [⟨s₀.gpr sc + BitVec.ofNat 64 st, 200⟩, ⟨s₀.gpr sc + BitVec.ofNat 64 wk, 640⟩] s₀.wr

section
variable (sc : Reg) (st wk : Nat) (s₀ : State)
abbrev STr : Region := ⟨s₀.gpr sc + BitVec.ofNat 64 st, 200⟩
abbrev WKr : Region := ⟨s₀.gpr sc + BitVec.ofNat 64 wk, 640⟩
end

/-- A piece the hash may read (`w = false`) or write (`w = true`). -/
structure PieceOk (sc : Reg) (st wk : Nat) (s₀ : State) (w : Bool) (p : Piece) : Prop where
  base : p.base ∈ preserved ∧ p.base ≠ .x30
  off : p.off < 65536
  len : p.len < 65536
  dst : (VG.Proof.MlKem.AArch64.preg s₀ p).Disjoint (VG.Proof.MlKem.AArch64.STr sc st s₀)
  dwk : (VG.Proof.MlKem.AArch64.preg s₀ p).Disjoint (VG.Proof.MlKem.AArch64.WKr sc wk s₀)
  stk : (VG.Proof.MlKem.AArch64.stk s₀).Disjoint (VG.Proof.MlKem.AArch64.preg s₀ p)
  cov : Covers [VG.Proof.MlKem.AArch64.preg s₀ p] (if w then s₀.wr else s₀.rd ++ s₀.wr)

theorem PieceOk.covW {sc : Reg} {st wk : Nat} {s₀ : State} {p : Piece} (h : VG.Proof.MlKem.AArch64.PieceOk sc st wk s₀ true p) :
    Covers [VG.Proof.MlKem.AArch64.preg s₀ p] s₀.wr := h.cov

/-- The position the next call starts from: 0 first, or the one the last
call returned. -/
def Pos (first : Bool) (s : State) : Nat := if first then 0 else (s.gpr .x0).toNat

theorem rate_bounds {r : Nat} (h : r ∈ rates) : 0 < r ∧ r ≤ 168 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h
  omega

theorem stk_sp {s s' : State} (h : s.sp = s'.sp) : VG.Proof.MlKem.AArch64.stk s = VG.Proof.MlKem.AArch64.stk s' := by
  unfold VG.Proof.MlKem.AArch64.stk; rw [h]

theorem below16 (sp : Addr) : below sp 16 = ⟨sp - 16, 16⟩ := rfl

theorem mem2' {α : Type} {a b x : α} (h : x ∈ [a, b]) : x = a ∨ x = b := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (List.mem_singleton.mp h)

theorem mem3 {α : Type} {a b c x : α} (h : x ∈ [a, b, c]) : x = a ∨ x = b ∨ x = c := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  rcases List.mem_cons.mp h with h | h
  · exact .inr (.inl h)
  · exact .inr (.inr (List.mem_singleton.mp h))

theorem mem4 {α : Type} {a b c d x : α} (h : x ∈ [a, b, c, d]) : x = a ∨ x = b ∨ x = c ∨ x = d := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (VG.Proof.MlKem.AArch64.mem3 h)

theorem mem5 {α : Type} {a b c d e x : α} (h : x ∈ [a, b, c, d, e]) :
    x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (VG.Proof.MlKem.AArch64.mem4 h)

theorem mem6 {α : Type} {a b c d e f x : α} (h : x ∈ [a, b, c, d, e, f]) :
    x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e ∨ x = f := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (VG.Proof.MlKem.AArch64.mem5 h)

theorem mem7 {α : Type} {a b c d e f g x : α} (h : x ∈ [a, b, c, d, e, f, g]) :
    x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e ∨ x = f ∨ x = g := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (VG.Proof.MlKem.AArch64.mem6 h)

theorem covers_one {R : Region} {rs : List Region} (h : R ∈ rs) : Covers [R] rs := fun _ _ hi => by
  obtain ⟨r, hr, hc⟩ := hi
  rw [List.mem_singleton.mp hr] at hc
  exact ⟨R, h, hc⟩

theorem covers_cons {R : Region} {rs xs : List Region} (h : Covers [R] xs) (h' : Covers rs xs) :
    Covers (R :: rs) xs := fun a n hi => by
  obtain ⟨r, hr, hc⟩ := hi
  rcases List.mem_cons.mp hr with rfl | hr
  · exact h a n ⟨r, List.mem_singleton_self _, hc⟩
  · exact h' a n ⟨r, hr, hc⟩

theorem Covers.head {R : Region} {rs xs : List Region} (h : Covers (R :: rs) xs) : Covers [R] xs :=
  fun a n ⟨r, hr, hc⟩ => h a n ⟨r, by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self .., hc⟩

theorem Covers.tail {R : Region} {rs xs : List Region} (h : Covers (R :: rs) xs) : Covers rs xs :=
  fun a n ⟨r, hr, hc⟩ => h a n ⟨r, List.mem_cons_of_mem _ hr, hc⟩

theorem covers_rw' {rs : List Region} {s : State} (h : Covers rs s.wr) : Covers rs (s.rd ++ s.wr) :=
  fun a n hi => in_rd_wr (h a n hi)

/-! ## The absorbs -/

theorem absorbsWith_ok (v : Proof.Sha3.AArch64.Permutation) {sc : Reg} {st wk rate : Nat} {s₀ : State} (hS : VG.Proof.MlKem.AArch64.HSetup sc st wk rate s₀) :
    ∀ (ps : List Piece) (first : Bool) (s : State) (msg : List Byte),
      (∀ p ∈ ps, VG.Proof.MlKem.AArch64.PieceOk sc st wk s₀ false p) →
      VG.Proof.MlKem.AArch64.Kept [VG.Proof.MlKem.AArch64.STr sc st s₀, VG.Proof.MlKem.AArch64.WKr sc wk s₀, below s₀.sp 16] s₀ s → Repr s.mem (s₀.gpr sc + BitVec.ofNat 64 st) rate msg →
      VG.Proof.MlKem.AArch64.Pos first s = msg.length % rate →
      WP isa (absorbsWith v.callee sc st wk rate first ps) s fun s' =>
        VG.Proof.MlKem.AArch64.Kept [VG.Proof.MlKem.AArch64.STr sc st s₀, VG.Proof.MlKem.AArch64.WKr sc wk s₀, below s₀.sp 16] s₀ s' ∧
        Repr s'.mem (s₀.gpr sc + BitVec.ofNat 64 st) rate (msg ++ (ps.map (VG.Proof.MlKem.AArch64.pbytes s₀)).flatten) ∧
        VG.Proof.MlKem.AArch64.Pos (first && ps.isEmpty) s' = (msg ++ (ps.map (VG.Proof.MlKem.AArch64.pbytes s₀)).flatten).length % rate := by
  intro ps
  induction ps with
  | nil => exact fun first s msg _ hk hr hpos => wp_nil ⟨hk, by simpa using hr, by simpa using hpos⟩
  | cons p ps ih =>
    intro first s msg hps hk hr hpos
    have hp := hps p (List.mem_cons_self ..)
    have rpos := (VG.Proof.MlKem.AArch64.rate_bounds hS.hrate).1
    have cs : ∀ r ∈ preserved, r ≠ .x30 → s.gpr r = s₀.gpr r := hk.cs
    have gsc := cs sc hS.hsc.1 hS.hsc.2
    have gb := cs p.base hp.base.1 hp.base.2
    have nsc := VG.Proof.MlKem.AArch64.pres_not hS.hsc.1
    have nb := VG.Proof.MlKem.AArch64.pres_not hp.base.1
    refine WP.seq ?_
    rw [keccakArgs, List.append_assoc, List.append_assoc, List.append_assoc]
    refine VG.Proof.MlKem.AArch64.wp_pos first fun s₁ h₁ e₁ => VG.Proof.MlKem.AArch64.wp_ptrTo (Ne.symm nsc.1) hS.hst fun s₂ h₂ e₂ =>
      wp_movz fun s₃ h₃ e₃ => VG.Proof.MlKem.AArch64.wp_ptrTo (Ne.symm nsc.2.2.2.2.2.1) hS.hwk fun s₄ h₄ e₄ => ?_
    refine VG.Proof.MlKem.AArch64.wp_ptrTo (Ne.symm nb.2.2.2.1) hp.off fun s₅ h₅ e₅ => wp_movz fun s₆ h₆ e₆ => wp_nil ?_
    have k₆ := (((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).keep
    have m₆ : s₆.mem = s.mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
    have hk₆ : VG.Proof.MlKem.AArch64.Kept [VG.Proof.MlKem.AArch64.STr sc st s₀, VG.Proof.MlKem.AArch64.WKr sc wk s₀, below s₀.sp 16] s₀ s₆ :=
      hk.trans (Kept.of_keep k₆ m₆ (by decide))
    have sp₆ : s₆.sp = s₀.sp := hk₆.sp
    have hpos' : VG.Proof.MlKem.AArch64.Pos first s < rate := by rw [hpos]; exact Nat.mod_lt _ rpos
    have c0 : s₆.gpr .x0 = s₀.gpr sc + BitVec.ofNat 64 st := by
      rw [h₆.get .x0, h₅.get .x0, h₄.get .x0, h₃.get .x0, e₂, h₁.get sc (by simpa using nsc.2.2.1), gsc]
    have c5 : s₆.gpr .x5 = s₀.gpr sc + BitVec.ofNat 64 wk := by
      rw [h₆.get .x5, h₅.get .x5, e₄, h₃.get sc (by simpa using nsc.2.1),
        h₂.get sc (by simpa using nsc.1), h₁.get sc (by simpa using nsc.2.2.1), gsc]
    have c3 : s₆.gpr .x3 = s₀.gpr p.base + BitVec.ofNat 64 p.off := by
      rw [h₆.get .x3, e₅, h₄.get p.base (by simpa using nb.2.2.2.2.2.1),
        h₃.get p.base (by simpa using nb.2.1), h₂.get p.base (by simpa using nb.1),
        h₁.get p.base (by simpa using nb.2.2.1), gb]
    refine WP.seq <| absorb_callWith v (rate := rate) (pos := VG.Proof.MlKem.AArch64.Pos first s) (len := p.len) c0
      (by rw [h₆.get .x1, h₅.get .x1, h₄.get .x1, e₃]; exact VG.Proof.MlKem.AArch64.imm16 (by have := (VG.Proof.MlKem.AArch64.rate_bounds hS.hrate).2; omega))
      (by rw [h₆.get .x2, h₅.get .x2, h₄.get .x2, h₃.get .x2, h₂.get .x2, e₁]; cases first <;> rfl)
      c3 (by rw [e₆]; exact VG.Proof.MlKem.AArch64.imm16 hp.len) c5 hS.hrate hpos' hS.d hp.dst hp.dwk (by rw [sp₆]; exact hS.sp16)
      (by rw [VG.Proof.MlKem.AArch64.stk_sp sp₆]; exact hS.kst) (by rw [VG.Proof.MlKem.AArch64.stk_sp sp₆]; exact hp.stk) (by rw [VG.Proof.MlKem.AArch64.stk_sp sp₆]; exact hS.kwk)
      (by rw [hk₆.rd, hk₆.wr]; exact VG.Proof.MlKem.AArch64.covers_cons hp.cov (VG.Proof.MlKem.AArch64.covers_rw' hS.cov)) (by rw [hk₆.wr]; exact hS.cov)
      fun s₇ k₇ r₇ ret₇ => ?_
    rw [sp₆] at k₇
    have hk₇ := hk₆.trans k₇
    have eb : bytesAt s₆.mem (s₀.gpr p.base + BitVec.ofNat 64 p.off) p.len = VG.Proof.MlKem.AArch64.pbytes s₀ p :=
      bytesAt_frame hk₆.frame (fun r hr => by
        rcases VG.Proof.MlKem.AArch64.mem3 hr with rfl | rfl | rfl
        · exact hp.dst
        · exact hp.dwk
        · rw [VG.Proof.MlKem.AArch64.below16]; exact hp.stk.symm) (by have := hp.len; omega)
    have rep := r₇ msg (by rw [m₆]; exact hr) hpos
    rw [eb] at rep
    refine WP.mono (ih false s₇ (msg ++ VG.Proof.MlKem.AArch64.pbytes s₀ p)
      (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hk₇ rep ?_) fun s' ⟨k', r', p'⟩ => ?_
    · show (s₇.gpr .x0).toNat = _
      rw [ret₇, hpos, List.length_append, bytesAt_length, Nat.mod_add_mod]
    · simp only [List.map_cons, List.flatten_cons, List.isEmpty_cons, Bool.and_false,
        ← List.append_assoc] at r' p' ⊢
      exact ⟨k', r', p'⟩

/-! ## The squeezes -/

/-- The registers and permissions `s₀` had. -/
structure Rg (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cs : ∀ r ∈ preserved, r ≠ .x30 → s.gpr r = s₀.gpr r

theorem Kept.rg {rs : List Region} {s₀ s : State} (h : VG.Proof.MlKem.AArch64.Kept rs s₀ s) : VG.Proof.MlKem.AArch64.Rg s₀ s := ⟨h.rd, h.wr, h.sp, h.cs⟩

theorem Rg.kept {rs : List Region} {s₀ s s' : State} (h : VG.Proof.MlKem.AArch64.Rg s₀ s) (hk : VG.Proof.MlKem.AArch64.Kept rs s s') : VG.Proof.MlKem.AArch64.Rg s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    fun r hr h30 => by rw [hk.cs r hr h30, h.cs r hr h30]⟩

/-- The output pieces hold consecutive output from the state `P`, from
position `c` on. -/
def Outs (s₀ : State) (m : Mem) (rate : Nat) (P : Spec.Sha3.State) : Nat → List Piece → Prop
  | _, [] => True
  | c, p :: ps => bytesAt m (s₀.gpr p.base + BitVec.ofNat 64 p.off) p.len = squeezeFrom rate P c p.len ∧
      VG.Proof.MlKem.AArch64.Outs s₀ m rate P (c + p.len) ps

theorem squeezesWith_ok (v : Proof.Sha3.AArch64.Permutation) {sc : Reg} {st wk rate : Nat} {s₀ : State} (hS : VG.Proof.MlKem.AArch64.HSetup sc st wk rate s₀)
    {P : Spec.Sha3.State} :
    ∀ (ps : List Piece) (first : Bool) (s : State) (c : Nat),
      (∀ p ∈ ps, VG.Proof.MlKem.AArch64.PieceOk sc st wk s₀ true p) → ps.Pairwise (fun p q => (VG.Proof.MlKem.AArch64.preg s₀ p).Disjoint (VG.Proof.MlKem.AArch64.preg s₀ q)) →
      VG.Proof.MlKem.AArch64.Rg s₀ s → VG.Proof.MlKem.AArch64.Pos first s ≤ rate →
      (∀ d, squeezeFrom rate (stateAt s.mem (s₀.gpr sc + BitVec.ofNat 64 st)) (VG.Proof.MlKem.AArch64.Pos first s) d =
        squeezeFrom rate P c d) →
      WP isa (squeezesWith v.callee sc st wk rate first ps) s fun s' =>
        VG.Proof.MlKem.AArch64.Kept (VG.Proof.MlKem.AArch64.STr sc st s₀ :: VG.Proof.MlKem.AArch64.WKr sc wk s₀ :: below s₀.sp 16 :: ps.map (VG.Proof.MlKem.AArch64.preg s₀)) s s' ∧
        VG.Proof.MlKem.AArch64.Outs s₀ s'.mem rate P c ps ∧ VG.Proof.MlKem.AArch64.Rg s₀ s' := by
  intro ps
  induction ps with
  | nil => exact fun first s c _ _ hg _ _ => wp_nil ⟨Kept.refl _ _, trivial, hg⟩
  | cons p ps ih =>
    intro first s c hps hpw hg hple hcont
    have hp := hps p (List.mem_cons_self ..)
    have ⟨rpos, rle⟩ := VG.Proof.MlKem.AArch64.rate_bounds hS.hrate
    have gsc := hg.cs sc hS.hsc.1 hS.hsc.2
    have gb := hg.cs p.base hp.base.1 hp.base.2
    have nsc := VG.Proof.MlKem.AArch64.pres_not hS.hsc.1
    have nb := VG.Proof.MlKem.AArch64.pres_not hp.base.1
    refine WP.seq ?_
    rw [keccakArgs, List.append_assoc, List.append_assoc, List.append_assoc]
    refine VG.Proof.MlKem.AArch64.wp_pos first fun s₁ h₁ e₁ => VG.Proof.MlKem.AArch64.wp_ptrTo (Ne.symm nsc.1) hS.hst fun s₂ h₂ e₂ =>
      wp_movz fun s₃ h₃ e₃ => VG.Proof.MlKem.AArch64.wp_ptrTo (Ne.symm nsc.2.2.2.2.2.1) hS.hwk fun s₄ h₄ e₄ => ?_
    refine VG.Proof.MlKem.AArch64.wp_ptrTo (Ne.symm nb.2.2.2.1) hp.off fun s₅ h₅ e₅ => wp_movz fun s₆ h₆ e₆ => wp_nil ?_
    have k₆ := (((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).keep
    have m₆ : s₆.mem = s.mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
    have kk₆ : VG.Proof.MlKem.AArch64.Kept [] s s₆ := Kept.of_keep k₆ m₆ (by decide)
    have hg₆ := hg.kept kk₆
    have sp₆ : s₆.sp = s₀.sp := hg₆.sp
    have c0 : s₆.gpr .x0 = s₀.gpr sc + BitVec.ofNat 64 st := by
      rw [h₆.get .x0, h₅.get .x0, h₄.get .x0, h₃.get .x0, e₂, h₁.get sc (by simpa using nsc.2.2.1), gsc]
    have c5 : s₆.gpr .x5 = s₀.gpr sc + BitVec.ofNat 64 wk := by
      rw [h₆.get .x5, h₅.get .x5, e₄, h₃.get sc (by simpa using nsc.2.1),
        h₂.get sc (by simpa using nsc.1), h₁.get sc (by simpa using nsc.2.2.1), gsc]
    have c3 : s₆.gpr .x3 = s₀.gpr p.base + BitVec.ofNat 64 p.off := by
      rw [h₆.get .x3, e₅, h₄.get p.base (by simpa using nb.2.2.2.2.2.1),
        h₃.get p.base (by simpa using nb.2.1), h₂.get p.base (by simpa using nb.1),
        h₁.get p.base (by simpa using nb.2.2.1), gb]
    refine WP.seq <| squeeze_callWith v (rate := rate) (pos := VG.Proof.MlKem.AArch64.Pos first s) (len := p.len) c0
      (by rw [h₆.get .x1, h₅.get .x1, h₄.get .x1, e₃]; exact VG.Proof.MlKem.AArch64.imm16 (by omega))
      (by rw [h₆.get .x2, h₅.get .x2, h₄.get .x2, h₃.get .x2, h₂.get .x2, e₁]; cases first <;> rfl)
      c3 (by rw [e₆]; exact VG.Proof.MlKem.AArch64.imm16 hp.len) c5 hS.hrate hple hp.dst.symm hS.d hp.dwk
      (by rw [sp₆]; exact hS.sp16) (by rw [VG.Proof.MlKem.AArch64.stk_sp sp₆]; exact hS.kst) (by rw [VG.Proof.MlKem.AArch64.stk_sp sp₆]; exact hp.stk)
      (by rw [VG.Proof.MlKem.AArch64.stk_sp sp₆]; exact hS.kwk)
      (by rw [hg₆.rd, hg₆.wr]; exact VG.Proof.MlKem.AArch64.covers_rw' (VG.Proof.MlKem.AArch64.covers_cons (Covers.head hS.cov) (VG.Proof.MlKem.AArch64.covers_cons hp.covW (Covers.tail hS.cov))))
      (by rw [hg₆.wr]; exact VG.Proof.MlKem.AArch64.covers_cons (Covers.head hS.cov) (VG.Proof.MlKem.AArch64.covers_cons hp.covW (Covers.tail hS.cov)))
      fun s₇ k₇ b₇ r₇ n₇ => ?_
    rw [sp₆] at k₇
    have hg₇ := hg₆.kept k₇
    have out₇ : bytesAt s₇.mem (s₀.gpr p.base + BitVec.ofNat 64 p.off) p.len = squeezeFrom rate P c p.len := by
      rw [b₇, m₆, hcont]
    have cont₇ : ∀ d, squeezeFrom rate (stateAt s₇.mem (s₀.gpr sc + BitVec.ofNat 64 st)) (VG.Proof.MlKem.AArch64.Pos false s₇) d =
        squeezeFrom rate P (c + p.len) d := fun d => by
      rw [show VG.Proof.MlKem.AArch64.Pos false s₇ = (s₇.gpr .x0).toNat from rfl, n₇, m₆]
      exact squeezeFrom_shift rpos (by omega) hcont p.len d
    have pw := List.pairwise_cons.mp hpw
    refine WP.mono (ih false s₇ (c + p.len) (fun q hq => hps q (List.mem_cons_of_mem _ hq)) pw.2 hg₇ r₇ cont₇)
      fun s' ⟨k', o', g'⟩ => ⟨?_, ⟨?_, o'⟩, g'⟩
    · refine (kk₆.mono (by simp)).trans ((k₇.mono fun r hr => ?_).trans (k'.mono fun r hr => ?_))
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact List.mem_cons_self ..
        rcases List.mem_cons.mp hr with rfl | hr
        · simp
        rcases VG.Proof.MlKem.AArch64.mem2' hr with rfl | rfl
        · simp
        · simp
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact List.mem_cons_self ..
        rcases List.mem_cons.mp hr with rfl | hr
        · simp
        rcases List.mem_cons.mp hr with rfl | hr
        · simp
        · simp [hr]
    · rw [← out₇]
      refine bytesAt_frame k'.frame (fun r hr => ?_) (by have := hp.len; omega)
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hp.dst
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hp.dwk
      rcases List.mem_cons.mp hr with rfl | hr
      · rw [VG.Proof.MlKem.AArch64.below16]; exact hp.stk.symm
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
        exact pw.1 q hq

/-! ## The whole hash -/

theorem zstores_ok (B : Addr) :
    ∀ n ≤ 25, ∀ {s : State}, s.gpr .x9 = 0 → s.gpr .x0 = B →
      (∀ k < 25, InRegions s.wr (B + BitVec.ofNat 64 (8 * k)) 8) →
      WP isa (.block ((List.range n).map fun k => .str .x .x9 .x0 (8 * k))) s fun s' =>
        s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
        (∀ k < n, s'.mem.readW (B + BitVec.ofNat 64 (8 * k)) 64 = 0) ∧ Frame [⟨B, 200⟩] s.mem s'.mem := by
  intro n
  induction n with
  | zero => exact fun _ _ _ _ _ => wp_nil ⟨rfl, rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _),
      Frame.refl _ _⟩
  | succ n ih =>
    intro hn s h9 h0 hin
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega) h9 h0 hin) fun s₁ ⟨g₁, r₁, w₁, p₁, z₁, f₁⟩ => ?_
    refine wp_strx (a := B + BitVec.ofNat 64 (8 * n)) (by constructor <;> omega) (by rw [g₁, h0])
      (by rw [w₁]; exact hin n (by omega)) fun s₂ h₂ => wp_nil ?_
    refine ⟨by rw [h₂.gpr, g₁], by rw [h₂.rd, r₁], by rw [h₂.wr, w₁], by rw [h₂.sp, p₁],
      fun k hk => ?_, ?_⟩
    · rw [h₂.mem, g₁, h9]
      by_cases e : k = n
      · subst e; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (sep_off _ (by omega) (by omega) (by omega)) (by decide)]
        exact z₁ k (by omega)
    · rw [h₂.mem]
      exact f₁.writeW (List.mem_singleton_self _) _ (contains_off (by omega) (by decide))

theorem stateAt_zero' {m : Mem} {p : Addr}
    (h : ∀ k < 25, m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = 0) : stateAt m p = Spec.Sha3.zero := by
  refine Vector.ext fun i hi => ?_
  simp only [stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
  exact h i hi

theorem zeroState_ok {sc : Reg} {st wk rate : Nat} {s₀ : State} (hS : VG.Proof.MlKem.AArch64.HSetup sc st wk rate s₀)
    {s : State} (hg : VG.Proof.MlKem.AArch64.Rg s₀ s) :
    WP isa (.block (zeroState sc st)) s fun s' =>
      VG.Proof.MlKem.AArch64.Kept [VG.Proof.MlKem.AArch64.STr sc st s₀] s s' ∧ stateAt s'.mem (s₀.gpr sc + BitVec.ofNat 64 st) = Spec.Sha3.zero := by
  have nsc := VG.Proof.MlKem.AArch64.pres_not hS.hsc.1
  refine VG.Proof.MlKem.AArch64.wp_ptrTo (Ne.symm nsc.1) hS.hst fun s₁ h₁ e₁ => wp_movz fun s₂ h₂ e₂ => ?_
  have hin : ∀ k < 25, InRegions s₂.wr (s₀.gpr sc + BitVec.ofNat 64 st + BitVec.ofNat 64 (8 * k)) 8 :=
    fun k hk => by
      rw [h₂.wr, h₁.wr, hg.wr]
      obtain ⟨r, hr, hc⟩ := Covers.head hS.cov (s₀.gpr sc + BitVec.ofNat 64 st + BitVec.ofNat 64 (8 * k)) 8
        ⟨_, List.mem_singleton_self _, contains_off (by omega) (by decide)⟩
      exact ⟨r, hr, hc⟩
  refine WP.mono (WP.preservedV (VG.Proof.MlKem.AArch64.zstores_ok _ 25 (by decide) (by rw [e₂]; rfl)
    (by rw [h₂.get .x0, e₁, hg.cs sc hS.hsc.1 hS.hsc.2]) hin) (hc := by lit_decide)) fun s' ⟨⟨g', r', w', p', z', f'⟩, hv⟩ => ?_
  have k₂ := (h₁.trans h₂).keep
  refine ⟨⟨fun r hr h30 => ?_, by rw [p', k₂.sp], by rw [r', k₂.rd], by rw [w', k₂.wr], ?_, fun r hr => (hv r hr).trans (k₂.vcs r hr)⟩,
    VG.Proof.MlKem.AArch64.stateAt_zero' fun k hk => z' k hk⟩
  · have := VG.Proof.MlKem.AArch64.pres_not hr
    rw [g', k₂.gpr r (by simp only [List.mem_append, List.mem_singleton, not_or]; exact ⟨this.1, this.2.2.2.2.2.2⟩)]
  · rw [h₂.mem, h₁.mem] at f'; exact f'

theorem sfx8 {sfx : Nat} (h : sfx < 256) :
    ((BitVec.ofNat 16 sfx).setWidth 64).setWidth 8 = BitVec.ofNat 8 sfx := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, VG.Proof.MlKem.AArch64.imm16 (by omega), BitVec.toNat_ofNat]

/-- `hash`: the sponge of the pieces `ins`, output into the pieces `outs`. -/
theorem hashWith_ok (v : Proof.Sha3.AArch64.Permutation) {sc : Reg} {st wk rate : Nat} {s₀ : State} (hS : VG.Proof.MlKem.AArch64.HSetup sc st wk rate s₀) {sfx : Nat}
    (hsfx : sfx < 256) {ins outs : List Piece} (hne : ins ≠ [])
    (hin : ∀ p ∈ ins, VG.Proof.MlKem.AArch64.PieceOk sc st wk s₀ false p) (hout : ∀ p ∈ outs, VG.Proof.MlKem.AArch64.PieceOk sc st wk s₀ true p)
    (hpw : outs.Pairwise (fun p q => (VG.Proof.MlKem.AArch64.preg s₀ p).Disjoint (VG.Proof.MlKem.AArch64.preg s₀ q))) :
    WP isa (hashWith v.callee sc st wk rate sfx ins outs) s₀ fun s' =>
      VG.Proof.MlKem.AArch64.Kept (VG.Proof.MlKem.AArch64.STr sc st s₀ :: VG.Proof.MlKem.AArch64.WKr sc wk s₀ :: below s₀.sp 16 :: outs.map (VG.Proof.MlKem.AArch64.preg s₀)) s₀ s' ∧
      VG.Proof.MlKem.AArch64.Outs s₀ s'.mem rate (absorb rate (pad rate (BitVec.ofNat 8 sfx) (ins.map (VG.Proof.MlKem.AArch64.pbytes s₀)).flatten)) 0 outs := by
  have ⟨rpos, rle⟩ := VG.Proof.MlKem.AArch64.rate_bounds hS.hrate
  have nsc := VG.Proof.MlKem.AArch64.pres_not hS.hsc.1
  have g0 : VG.Proof.MlKem.AArch64.Rg s₀ s₀ := ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩
  refine WP.seq (WP.mono (VG.Proof.MlKem.AArch64.zeroState_ok hS g0) fun s₁ ⟨k₁, z₁⟩ => ?_)
  refine WP.seq (WP.mono ((VG.Proof.MlKem.AArch64.absorbsWith_ok v) hS ins true s₁ [] hin (k₁.mono (by simp)) (repr_nil z₁)
    (by rfl)) fun s₂ ⟨k₂, r₂, p₂⟩ => ?_)
  have hie : ins.isEmpty = false := by cases ins; exact absurd rfl hne; rfl
  rw [hie, Bool.and_false, List.nil_append] at p₂
  rw [List.nil_append] at r₂
  refine WP.seq ?_
  rw [keccakArgs, List.append_assoc, List.append_assoc]
  refine VG.Proof.MlKem.AArch64.wp_pos false fun s₃ h₃ e₃ => VG.Proof.MlKem.AArch64.wp_ptrTo (Ne.symm nsc.1) hS.hst fun s₄ h₄ e₄ =>
    wp_movz fun s₅ h₅ e₅ => VG.Proof.MlKem.AArch64.wp_ptrTo (Ne.symm nsc.2.2.2.2.1) hS.hwk fun s₆ h₆ e₆ => wp_movz
    fun s₇ h₇ e₇ => wp_nil ?_
  have k₇ := ((((h₃.trans h₄).trans h₅).trans h₆).trans h₇).keep
  have m₇ : s₇.mem = s₂.mem := by rw [h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem]
  have kk₇ : VG.Proof.MlKem.AArch64.Kept [] s₂ s₇ := Kept.of_keep k₇ m₇ (by decide)
  have hg₇ := k₂.rg.kept kk₇
  have gsc := k₂.cs sc hS.hsc.1 hS.hsc.2
  have sp₇ : s₇.sp = s₀.sp := hg₇.sp
  refine WP.seq <| pad_callWith v (st := s₀.gpr sc + BitVec.ofNat 64 st) (sc := s₀.gpr sc + BitVec.ofNat 64 wk)
    (rate := rate) (pos := (s₂.gpr .x0).toNat)
    (by rw [h₇.get .x0, h₆.get .x0, h₅.get .x0, e₄, h₃.get sc (by simpa using nsc.2.2.1), gsc])
    (by rw [h₇.get .x1, h₆.get .x1, e₅]; exact VG.Proof.MlKem.AArch64.imm16 (by omega))
    (by rw [h₇.get .x2, h₆.get .x2, h₅.get .x2, h₄.get .x2, e₃]; rfl)
    (by rw [h₇.get .x4, e₆, h₅.get sc (by simpa using nsc.2.1), h₄.get sc (by simpa using nsc.1),
      h₃.get sc (by simpa using nsc.2.2.1), gsc])
    hS.hrate (by have : (s₂.gpr .x0).toNat = _ := p₂; rw [this]; exact Nat.mod_lt _ rpos) hS.d
    (by rw [sp₇]; exact hS.sp16) (by rw [VG.Proof.MlKem.AArch64.stk_sp sp₇]; exact hS.kst) (by rw [VG.Proof.MlKem.AArch64.stk_sp sp₇]; exact hS.kwk)
    (by rw [hg₇.rd, hg₇.wr]; exact VG.Proof.MlKem.AArch64.covers_rw' hS.cov) (by rw [hg₇.wr]; exact hS.cov) fun s₈ k₈ r₈ => ?_
  rw [sp₇] at k₈
  have st₈ := r₈ _ (by rw [m₇]; exact r₂) p₂
  rw [show (s₇.gpr .x3).setWidth 8 = BitVec.ofNat 8 sfx by rw [e₇]; exact VG.Proof.MlKem.AArch64.sfx8 hsfx] at st₈
  have hg₈ := hg₇.kept k₈
  refine WP.mono ((VG.Proof.MlKem.AArch64.squeezesWith_ok v) hS (P := absorb rate (pad rate (BitVec.ofNat 8 sfx) (ins.map (VG.Proof.MlKem.AArch64.pbytes s₀)).flatten))
    outs true s₈ 0 hout hpw hg₈ (Nat.zero_le _) (fun d => by rw [st₈]; rfl)) fun s' ⟨k', o', _⟩ => ⟨?_, o'⟩
  refine (k₂.mono fun r hr => ?_).trans ((kk₇.mono (by simp)).trans ((k₈.mono fun r hr => ?_).trans k'))
  · rcases VG.Proof.MlKem.AArch64.mem3 hr with rfl | rfl | rfl <;> simp
  · rcases VG.Proof.MlKem.AArch64.mem3 hr with rfl | rfl | rfl <;> simp

theorem hash_ok {sc : Reg} {st wk rate : Nat} {s₀ : State} (hS : VG.Proof.MlKem.AArch64.HSetup sc st wk rate s₀) {sfx : Nat}
    (hsfx : sfx < 256) {ins outs : List Piece} (hne : ins ≠ [])
    (hin : ∀ p ∈ ins, VG.Proof.MlKem.AArch64.PieceOk sc st wk s₀ false p) (hout : ∀ p ∈ outs, VG.Proof.MlKem.AArch64.PieceOk sc st wk s₀ true p)
    (hpw : outs.Pairwise (fun p q => (VG.Proof.MlKem.AArch64.preg s₀ p).Disjoint (VG.Proof.MlKem.AArch64.preg s₀ q))) :
    WP isa (hash sc st wk rate sfx ins outs) s₀ fun s' =>
      VG.Proof.MlKem.AArch64.Kept (VG.Proof.MlKem.AArch64.STr sc st s₀ :: VG.Proof.MlKem.AArch64.WKr sc wk s₀ :: below s₀.sp 16 :: outs.map (VG.Proof.MlKem.AArch64.preg s₀)) s₀ s' ∧
      VG.Proof.MlKem.AArch64.Outs s₀ s'.mem rate (absorb rate (pad rate (BitVec.ofNat 8 sfx) (ins.map (VG.Proof.MlKem.AArch64.pbytes s₀)).flatten)) 0 outs :=
  VG.Proof.MlKem.AArch64.hashWith_ok .scalar hS hsfx hne hin hout hpw

end VG.Proof.MlKem.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.MemTaint`. -/
section

/-!
# Taint tracking over memory both runs agree on (AArch64)

The taint analysis (`Proof/Framework/AArch64/Taint.lean`) treats memory as
secret. `memTaint` is one for code that runs with permissions only on
memory whose bytes two runs agree on (`MemEq`): every load it can make is
then public, and a store keeps the agreement if it stores a public value at
a public address. It proves constant time for code whose branches and
addresses depend on the contents of such memory, e.g. rejection sampling
from an output that is a function of the declared leak.

`RelCT.narrow` applies it to code that runs with more permissions but only
touches memory the two runs agree on: the runs from the states narrowed to
those regions leak what the actual runs leak (`Exec.widen` and determinism).
-/

namespace VG.AArch64.MemTaint

open VG.AArch64.Taint (T pub set)

/-- `m₁` and `m₂` agree on every byte of the regions `rs`. -/
def MemEq (rs : List Region) (m₁ m₂ : Mem) : Prop := ∀ x, InRegions rs x 1 → m₁ x = m₂ x

/-- The registers `τ` agree, and the permissions and the memory they permit. -/
def Agree (τ : VG.AArch64.Taint.T) (s₁ s₂ : VG.AArch64.State) : Prop :=
  Taint.Agree τ s₁ s₂ ∧ s₁.rd = s₂.rd ∧ s₁.wr = s₂.wr ∧ VG.AArch64.MemTaint.MemEq (s₁.rd ++ s₁.wr) s₁.mem s₂.mem

/-- Instructions that only write a general-purpose register. -/
def regOp : Instr → Bool
  | .add .. | .sub .. | .addImm .. | .subImm .. | .logic .. | .ror .. | .lsr .. | .lsl .. | .madd ..
  | .mul .. | .rev32 .. | .rev .. | .movz .. | .movk .. => true
  | _ => false

/-- Loads are public, stores must store public values; the other memory
instructions and frames are not analysed. -/
def step (τ : VG.AArch64.Taint.T) : Instr → Option VG.AArch64.Taint.T
  | .ldr _ t n _ | .ldrb t n _ => if pub τ n then some (set τ t true) else none
  | .str _ t n _ | .strb t n _ => if pub τ n && pub τ t then some τ else none
  | i => if VG.AArch64.MemTaint.regOp i then Taint.step τ i else none

theorem exec_regOp {i : Instr} (hi : VG.AArch64.MemTaint.regOp i = true) {s s' : VG.AArch64.State} (h : exec i s = some s') :
    s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  cases i <;> simp [VG.AArch64.MemTaint.regOp] at hi <;> simp only [exec] at h <;>
    first
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩)
    | (split at h <;> [skip; cases h]
       simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩)

theorem MemEq.read {rs : List Region} {m₁ m₂ : Mem} (h : VG.AArch64.MemTaint.MemEq rs m₁ m₂) {a : Addr} {n : Nat}
    (hi : InRegions rs a n) (hn : n < 2 ^ 64) : m₁.read a n = m₂.read a n := by
  obtain ⟨r, hr, hc⟩ := hi
  exact Mem.read_congr fun i hi' =>
    h _ ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat a (by omega)]; exact hi')⟩

theorem MemEq.write {rs : List Region} {m₁ m₂ : Mem} (h : VG.AArch64.MemTaint.MemEq rs m₁ m₂) (a : Addr) (n : Nat)
    (v : BitVec (8 * n)) : VG.AArch64.MemTaint.MemEq rs (m₁.write a n v) (m₂.write a n v) := fun x hx => by
  simp only [Mem.write]
  split
  · rfl
  · exact h x hx

theorem regOp_sound {τ τ' : VG.AArch64.Taint.T} {i : Instr} (hr : VG.AArch64.MemTaint.regOp i = true) {s₁ s₂ s₁' s₂' : VG.AArch64.State}
    (ha : VG.AArch64.MemTaint.Agree τ s₁ s₂) (hs : Taint.step τ i = some τ') (e₁ : exec i s₁ = some s₁')
    (e₂ : exec i s₂ = some s₂') : addrs i s₁ = addrs i s₂ ∧ VG.AArch64.MemTaint.Agree τ' s₁' s₂' := by
  obtain ⟨hadd, ht⟩ := Taint.step_sound ha.1 hs e₁ e₂
  obtain ⟨m₁, r₁, w₁⟩ := VG.AArch64.MemTaint.exec_regOp hr e₁
  obtain ⟨m₂, r₂, w₂⟩ := VG.AArch64.MemTaint.exec_regOp hr e₂
  exact ⟨hadd, ht, by rw [r₁, r₂, ha.2.1], by rw [w₁, w₂, ha.2.2.1], by
    rw [m₁, m₂, r₁, w₁]; exact ha.2.2.2⟩

theorem load_sound {τ : VG.AArch64.Taint.T} {s₁ s₂ : VG.AArch64.State} (ha : VG.AArch64.MemTaint.Agree τ s₁ s₂) {n : Reg} (hn : pub τ n = true)
    (bytes off : Nat) {a₁ a₂ : Addr} (h₁ : addr s₁ bytes n off = some a₁)
    (h₂ : addr s₂ bytes n off = some a₂) {v₁ v₂ : BitVec (8 * bytes)}
    (l₁ : s₁.load a₁ bytes = some v₁) (l₂ : s₂.load a₂ bytes = some v₂) (hb : bytes < 2 ^ 64) :
    v₁ = v₂ := by
  have ea : a₁ = a₂ := by
    simp only [addr, ha.1.reg hn] at h₁ h₂
    split at h₁ <;> [rename_i hc; cases h₁]
    rw [ite_eq_left hc] at h₂
    exact (Option.some.inj h₁).symm.trans (Option.some.inj h₂)
  subst ea
  simp only [State.load] at l₁ l₂
  split at l₁ <;> [rename_i hi; cases l₁]
  split at l₂ <;> [skip; cases l₂]
  cases l₁; cases l₂
  exact ha.2.2.2.read hi hb

theorem store_sound {τ : VG.AArch64.Taint.T} {s₁ s₂ : VG.AArch64.State} (ha : VG.AArch64.MemTaint.Agree τ s₁ s₂) {n : Reg} (hn : pub τ n = true)
    (bytes off : Nat) {a₁ a₂ : Addr} (h₁ : addr s₁ bytes n off = some a₁)
    (h₂ : addr s₂ bytes n off = some a₂) {v : BitVec (8 * bytes)} {s₁' s₂' : VG.AArch64.State}
    (e₁ : s₁.store a₁ bytes v = some s₁') (e₂ : s₂.store a₂ bytes v = some s₂') :
    VG.AArch64.MemTaint.Agree τ s₁' s₂' := by
  have ea : a₁ = a₂ := by
    simp only [addr, ha.1.reg hn] at h₁ h₂
    split at h₁ <;> [rename_i hc; cases h₁]
    rw [ite_eq_left hc] at h₂
    exact (Option.some.inj h₁).symm.trans (Option.some.inj h₂)
  subst ea
  simp only [State.store] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  exact ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.write _ _ _⟩

theorem step_sound {τ τ' : VG.AArch64.Taint.T} {i : Instr} {s₁ s₂ s₁' s₂' : VG.AArch64.State} (ha : VG.AArch64.MemTaint.Agree τ s₁ s₂)
    (hs : VG.AArch64.MemTaint.step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ VG.AArch64.MemTaint.Agree τ' s₁' s₂' := by
  cases i with
  | ldr sz t n off =>
    simp only [VG.AArch64.MemTaint.step] at hs
    split at hs <;> [rename_i hn; cases hs]
    cases hs
    refine ⟨by simp [addrs, ha.1.reg hn], ?_⟩
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨a₁, h₁, v₁, l₁, rfl⟩ := e₁; obtain ⟨a₂, h₂, v₂, l₂, rfl⟩ := e₂
    have hv := VG.AArch64.MemTaint.load_sound ha hn _ off h₁ h₂ l₁ l₂ (by cases sz <;> decide)
    subst hv
    exact ⟨ha.1.write sz t fun _ => rfl, ha.2⟩
  | ldrb t n off =>
    simp only [VG.AArch64.MemTaint.step] at hs
    split at hs <;> [rename_i hn; cases hs]
    cases hs
    refine ⟨by simp [addrs, ha.1.reg hn], ?_⟩
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e₁ e₂
    obtain ⟨a₁, h₁, v₁, l₁, rfl⟩ := e₁; obtain ⟨a₂, h₂, v₂, l₂, rfl⟩ := e₂
    have hv := VG.AArch64.MemTaint.load_sound ha hn _ off h₁ h₂ l₁ l₂ (by decide)
    subst hv
    exact ⟨ha.1.write .w t fun _ => rfl, ha.2⟩
  | str sz t n off =>
    simp only [VG.AArch64.MemTaint.step] at hs
    split at hs <;> [rename_i hn; cases hs]
    cases hs
    simp only [Bool.and_eq_true] at hn
    refine ⟨by simp [addrs, ha.1.reg hn.1], ?_⟩
    simp only [exec, Option.bind_eq_some_iff] at e₁ e₂
    obtain ⟨a₁, h₁, e₁⟩ := e₁; obtain ⟨a₂, h₂, e₂⟩ := e₂
    rw [ha.1.read hn.2] at e₁
    exact VG.AArch64.MemTaint.store_sound ha hn.1 _ off h₁ h₂ e₁ e₂
  | strb t n off =>
    simp only [VG.AArch64.MemTaint.step] at hs
    split at hs <;> [rename_i hn; cases hs]
    cases hs
    simp only [Bool.and_eq_true] at hn
    refine ⟨by simp [addrs, ha.1.reg hn.1], ?_⟩
    simp only [exec, Option.bind_eq_some_iff] at e₁ e₂
    obtain ⟨a₁, h₁, e₁⟩ := e₁; obtain ⟨a₂, h₂, e₂⟩ := e₂
    rw [ha.1.read hn.2] at e₁
    exact VG.AArch64.MemTaint.store_sound ha hn.1 _ off h₁ h₂ e₁ e₂
  | _ =>
    simp only [VG.AArch64.MemTaint.step] at hs
    split at hs <;> [rename_i hr; cases hs]
    exact VG.AArch64.MemTaint.regOp_sound hr ha hs e₁ e₂

theorem cond_sound {τ : VG.AArch64.Taint.T} {c : Cond} {s₁ s₂ : VG.AArch64.State} (ha : VG.AArch64.MemTaint.Agree τ s₁ s₂)
    (hc : Taint.condPub τ c = true) : VG.AArch64.eval c s₁ = VG.AArch64.eval c s₂ :=
  Taint.cond_sound ha.1 hc

end VG.AArch64.MemTaint

namespace VG.AArch64

open MemTaint in
/-- Taint tracking over memory both runs agree on, for AArch64. -/
def memTaint : VG.Taint isa where
  T := Taint.T
  Agree := MemTaint.Agree
  step := MemTaint.step
  step_sound := MemTaint.step_sound
  condPub := Taint.condPub
  cond_sound := MemTaint.cond_sound
  meet τ₁ τ₂ := τ₁.inter τ₂
  meet_left h := ⟨taint.meet_left h.1, h.2⟩
  meet_right h := ⟨taint.meet_right h.1, h.2⟩
  le τ σ := τ.subset σ
  le_sound hle h := ⟨taint.le_sound hle h.1, h.2⟩
  call _ := none
  call_sound _ hs _ _ := by cases hs
  ret _ := none
  ret_sound _ hs _ _ := by cases hs
  push _ _ := none
  push_sound _ hs _ _ := by cases hs
  pop _ _ := none
  pop_sound _ hs _ _ := by cases hs

/-- Code run with more permissions than the regions `rd` and `wr` it
touches: if the runs from the states narrowed to them exist, and those
leak the same traces, so do the actual runs. -/
theorem RelCT.narrow {c : Prog isa} {P : VG.AArch64.State → VG.AArch64.State → Prop} {Q : VG.AArch64.State → VG.AArch64.State → Prop}
    (rd wr : List Region)
    (hc : ∀ s₁ s₂, P s₁ s₂ → (Covers (rd ++ wr) (s₁.rd ++ s₁.wr) ∧ Covers wr s₁.wr) ∧
      (Covers (rd ++ wr) (s₂.rd ++ s₂.wr) ∧ Covers wr s₂.wr))
    (hw : ∀ s₁ s₂, P s₁ s₂ →
      (∃ t s', Exec isa c (s₁.withRegions rd wr) t s') ∧ ∃ t s', Exec isa c (s₂.withRegions rd wr) t s')
    (h : RelCT isa (fun u₁ u₂ => ∃ s₁ s₂, P s₁ s₂ ∧ u₁ = s₁.withRegions rd wr ∧
      u₂ = s₂.withRegions rd wr) c Q) :
    RelCT isa P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨⟨c₁, w₁⟩, ⟨c₂, w₂⟩⟩ := hc _ _ hp
  obtain ⟨⟨u₁, v₁, n₁⟩, ⟨u₂, v₂, n₂⟩⟩ := hw _ _ hp
  have x₁ := Exec.widen n₁ (rd := s₁.rd) (wr := s₁.wr) (by simpa using c₁) (by simpa using w₁)
  have x₂ := Exec.widen n₂ (rd := s₂.rd) (wr := s₂.wr) (by simpa using c₂) (by simpa using w₂)
  simp only [State.withRegions_withRegions, State.withRegions_self] at x₁ x₂
  obtain ⟨rfl, -⟩ := Exec.det e₁ x₁
  obtain ⟨rfl, -⟩ := Exec.det e₂ x₂
  exact ⟨(h _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ n₁ n₂).1, trivial⟩

end VG.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.SampleLoop`. -/
section

/-!
# ML-KEM on AArch64: the loop of `SampleNTT`

`N` iterations of the loop of `SampleNTT` on the SHAKE128 output `xofByte B`
at `bP` compute `sampleAfter [] (xofByte B) N` (`Proof/MlKem/KPke.lean`) into
`a`, which starts as zeros (`iters_ok`); after 280 of them, `sampleLoop`
returns whether it has 256 coefficients (`loop_ok`). The loop reads only the
output, and writes only `a`.
-/

namespace VG.Proof.MlKem.AArch64.Sample

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem

/-- What `N` iterations of the loop need of the state they start in: the
first `3N` bytes of the output of SHAKE128 of `B` at `bP`, which they may
read; zeros at `aP`, which they may write. -/
structure LPre (N : Nat) (B : List Byte) (bP aP : Addr) (s : State) : Prop where
  buf : ∀ p < 3 * N, s.mem (bP + BitVec.ofNat 64 p) = xofByte B p
  inb : ∀ p < 3 * N, InRegions (s.rd ++ s.wr) (bP + BitVec.ofNat 64 p) 1
  ina : ∀ i < 256, InRegions s.wr (coeffAddr aP i) 4
  disj : (⟨bP, 3 * N⟩ : Region).Disjoint (polyRegion aP)
  zero : ∀ i < 256, coeffAt s.mem aP i = 0
  x2 : s.gpr .x2 = bP
  x3 : s.gpr .x3 = aP
  x4 : (s.gpr .x4).toNat = 256
  x5 : (s.gpr .x5).toNat = N
  x9 : (s.gpr .x9).toNat = VG.Spec.MlKem.q
  x10 : (s.gpr .x10).toNat = 15
  bound : N ≤ 280

/-- Coefficient `i` of the list `L`, as stored. -/
def cv (L : List VG.Spec.MlKem.Zq) (i : Nat) : BitVec 32 := BitVec.ofNat 32 (L.getD i 0).val

/-- The coefficients `L` at `aP`, and zeros after them but for coefficient
`L.length`, which may hold a rejected candidate. -/
def Coeffs (m : Mem) (aP : Addr) (L : List VG.Spec.MlKem.Zq) : Prop :=
  ∀ i < 256, i ≠ L.length → coeffAt m aP i = if i < L.length then VG.Proof.MlKem.AArch64.Sample.cv L i else 0

/-- The coefficients accepted so far, `L`, stored at `aP`, with zeros after
them (`Coeffs`); the permissions, and all memory outside `a`, as in `s₀`. -/
structure Acc (aP : Addr) (s₀ : State) (L : List VG.Spec.MlKem.Zq) (u : State) : Prop where
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr
  sp : u.sp = s₀.sp
  len : L.length ≤ 256
  x3 : u.gpr .x3 = coeffAddr aP L.length
  x4 : (u.gpr .x4).toNat = 256 - L.length
  x9 : (u.gpr .x9).toNat = VG.Spec.MlKem.q
  coeffs : VG.Proof.MlKem.AArch64.Sample.Coeffs u.mem aP L
  frame : VG.Frame [polyRegion aP] s₀.mem u.mem

theorem cv_append (L : List VG.Spec.MlKem.Zq) (x : VG.Spec.MlKem.Zq) {i : Nat} (hi : i < L.length) : VG.Proof.MlKem.AArch64.Sample.cv L i = VG.Proof.MlKem.AArch64.Sample.cv (L ++ [x]) i := by
  simp only [VG.Proof.MlKem.AArch64.Sample.cv, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem cv_last (L : List VG.Spec.MlKem.Zq) (x : VG.Spec.MlKem.Zq) : VG.Proof.MlKem.AArch64.Sample.cv (L ++ [x]) L.length = BitVec.ofNat 32 x.val := by
  simp [VG.Proof.MlKem.AArch64.Sample.cv]

theorem Coeffs.full {m : Mem} {aP : Addr} {L : List VG.Spec.MlKem.Zq} (h : VG.Proof.MlKem.AArch64.Sample.Coeffs m aP L) (hf : L.length = 256) :
    CoeffsUpTo m aP L.length (VG.Proof.MlKem.AArch64.Sample.cv L) fun _ => 0 :=
  fun i hi => h i hi (by omega)

/-- Coefficient `L.length` set to zero. -/
theorem Coeffs.zero {m : Mem} {aP : Addr} {L : List VG.Spec.MlKem.Zq} (h : VG.Proof.MlKem.AArch64.Sample.Coeffs m aP L) (hl : L.length < 256) :
    CoeffsUpTo (m.writeW (coeffAddr aP L.length) (0 : BitVec 32)) aP L.length (VG.Proof.MlKem.AArch64.Sample.cv L) fun _ => 0 := fun i hi => by
  rw [coeffAt_writeW m aP (show i < VG.Spec.MlKem.n from hi) (show L.length < VG.Spec.MlKem.n from hl)]
  by_cases e : L.length = i
  · rw [ite_eq_left e, ite_eq_right (by omega)]
  · rw [ite_eq_right e, h i hi (Ne.symm e)]

/-- A rejected candidate stored as coefficient `L.length`. -/
theorem Coeffs.reject {m : Mem} {aP : Addr} {L : List VG.Spec.MlKem.Zq} (h : VG.Proof.MlKem.AArch64.Sample.Coeffs m aP L) (hl : L.length < 256)
    (w : BitVec 32) : VG.Proof.MlKem.AArch64.Sample.Coeffs (m.writeW (coeffAddr aP L.length) w) aP L := fun i hi hne => by
  rw [coeffAt_writeW_ne m aP (show i < VG.Spec.MlKem.n from hi) (show L.length < VG.Spec.MlKem.n from hl) hne, h i hi hne]

/-- An accepted candidate `x` stored as coefficient `L.length`. -/
theorem Coeffs.accept {m : Mem} {aP : Addr} {L : List VG.Spec.MlKem.Zq} (h : VG.Proof.MlKem.AArch64.Sample.Coeffs m aP L) (hl : L.length < 256)
    {x : VG.Spec.MlKem.Zq} {w : BitVec 32} (hw : w = BitVec.ofNat 32 x.val) :
    VG.Proof.MlKem.AArch64.Sample.Coeffs (m.writeW (coeffAddr aP L.length) w) aP (L ++ [x]) := fun i hi hne => by
  rw [coeffAt_writeW m aP (show i < VG.Spec.MlKem.n from hi) (show L.length < VG.Spec.MlKem.n from hl)]
  simp only [List.length_append, List.length_singleton] at hne ⊢
  by_cases e : L.length = i
  · subst e
    rw [ite_eq_left rfl, ite_eq_left (by omega), VG.Proof.MlKem.AArch64.Sample.cv_last, hw]
  · rw [ite_eq_right e, h i hi (Ne.symm e)]
    by_cases hit : i < L.length
    · rw [ite_eq_left hit, ite_eq_left (by omega), VG.Proof.MlKem.AArch64.Sample.cv_append L x hit]
    · rw [ite_eq_right hit, ite_eq_right (by omega)]

/-- `v - q`, negative exactly when `v < q`. -/
theorem lt_q_arith {a b : BitVec 64} {v : Nat} (ha : a.toNat = v) (hv : v < 2 ^ 12)
    (hb : b.toNat = VG.Spec.MlKem.q) : ((a - b) >>> 63).toNat = if v < VG.Spec.MlKem.q then 1 else 0 := by
  rw [toNat_lsr, BitVec.toNat_sub, ha, hb]
  have hq : VG.Spec.MlKem.q = 3329 := rfl
  split <;> omega

/-- Accepting the candidate `v` in `d` if it is less than `q`: storing it
either way, and counting it only if it is accepted. -/
theorem accept_ok {aP : Addr} {s₀ : State} (hina : ∀ i < 256, InRegions s₀.wr (coeffAddr aP i) 4)
    {L : List VG.Spec.MlKem.Zq} {u : State} (h : VG.Proof.MlKem.AArch64.Sample.Acc aP s₀ L u) (hlt : L.length < 256) {d : Reg}
    (hd : d ≠ .x13 ∧ d ≠ .x14) {v : Nat} (hv : (u.gpr d).toNat = v) (hv' : v < 2 ^ 12) :
    WP isa (.block (sampleAccept d)) u fun u' =>
      VG.Proof.MlKem.AArch64.Sample.Acc aP s₀ (if v < VG.Spec.MlKem.q then L ++ [ofNat v] else L) u' ∧
        Keep [.x3, .x4, .x13, .x14, .x15] u u' := by
  have hq : VG.Spec.MlKem.q = 3329 := rfl
  refine VG.Proof.MlKem.AArch64.wp_sub fun u₁ h₁ e₁ => VG.Proof.MlKem.AArch64.wp_lsr (by decide) fun u₂ h₂ e₂ => ?_
  have v14 : (u₂.gpr .x14).toNat = if v < VG.Spec.MlKem.q then 1 else 0 := by
    rw [e₂, e₁]
    exact VG.Proof.MlKem.AArch64.Sample.lt_q_arith hv hv' h.x9
  have dv : (u₂.gpr d).toNat = v := by
    rw [h₂.gpr d (by simpa using hd.2), h₁.gpr d (by simpa using hd.1), hv]
  refine wp_strw (a := coeffAddr aP L.length) (by decide)
    (by rw [h₂.gpr .x3 (by decide), h₁.gpr .x3 (by decide), h.x3, ptr_zero])
    (by rw [h₂.wr, h₁.wr, h.wr]; exact hina _ hlt) fun u₃ h₃ =>
    wp_lsl (by decide) fun u₄ h₄ e₄ => VG.Proof.MlKem.AArch64.wp_add fun u₅ h₅ e₅ => VG.Proof.MlKem.AArch64.wp_sub fun u₆ h₆ e₆ => VG.Proof.MlKem.AArch64.wp_nil ?_
  have k₆ := (((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans
    h₆.keep).mono (rs' := [.x3, .x4, .x13, .x14, .x15]) (by decide)
  have m₆ : u₆.mem = u.mem.writeW (coeffAddr aP L.length) ((u₂.gpr d).setWidth 32) := by
    rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have x14 : u₅.gpr .x14 = u₂.gpr .x14 := by
    rw [h₅.gpr .x14 (by decide), h₄.gpr .x14 (by decide), h₃.gpr]
  have x15 : u₄.gpr .x15 = BitVec.ofNat 64 (4 * if v < VG.Spec.MlKem.q then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [e₄, toNat_lsl_n (by rw [h₃.gpr, v14]; split <;> decide), h₃.gpr, v14, BitVec.toNat_ofNat]
    split <;> decide
  have x3 : u₆.gpr .x3 = coeffAddr aP (L.length + if v < VG.Spec.MlKem.q then 1 else 0) := by
    rw [h₆.gpr .x3 (by decide), e₅, h₄.gpr .x3 (by decide), h₃.gpr, h₂.gpr .x3 (by decide),
      h₁.gpr .x3 (by decide), h.x3, x15, coeffAddr, coeffAddr, ptr_add, Nat.mul_add]
  have c4 : (u₅.gpr .x4).toNat = 256 - L.length := by
    rw [h₅.gpr .x4 (by decide), h₄.gpr .x4 (by decide), h₃.gpr, h₂.gpr .x4 (by decide),
      h₁.gpr .x4 (by decide), h.x4]
  have x4 : (u₆.gpr .x4).toNat = 256 - L.length - if v < VG.Spec.MlKem.q then 1 else 0 := by
    rw [e₆, toNat_sub_n (by rw [x14, v14, c4]; split <;> omega), c4, x14, v14]
  have fr : VG.Frame [polyRegion aP] s₀.mem u₆.mem := by
    rw [m₆]
    exact h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ (show L.length < VG.Spec.MlKem.n from hlt))
  have acc : ∀ L' : List VG.Spec.MlKem.Zq, L'.length = L.length + (if v < VG.Spec.MlKem.q then 1 else 0) →
      VG.Proof.MlKem.AArch64.Sample.Coeffs u₆.mem aP L' → VG.Proof.MlKem.AArch64.Sample.Acc aP s₀ L' u₆ := fun L' hl hc =>
    ⟨by rw [k₆.rd, h.rd], by rw [k₆.wr, h.wr], by rw [k₆.sp, h.sp], by rw [hl]; split <;> omega,
      by rw [x3, hl], by rw [x4, hl]; split <;> omega, by rw [k₆.get .x9, h.x9], hc, fr⟩
  refine ⟨acc _ ?_ ?_, k₆⟩
  · split <;> simp
  · rw [m₆]
    by_cases hvq : v < VG.Spec.MlKem.q
    · rw [ite_eq_left hvq]
      exact h.coeffs.accept hlt (by rw [setWidth32_of_toNat dv, val_ofNat, Nat.mod_eq_of_lt hvq])
    · rw [ite_eq_right hvq]
      exact h.coeffs.reject hlt _

/-! ## One iteration -/

/-- The first candidate of chunk `t`. -/
abbrev d₁ (B : List Byte) (t : Nat) : Nat :=
  (xofByte B (3 * t)).toNat + 256 * ((xofByte B (3 * t + 1)).toNat % 16)

/-- The second candidate of chunk `t`. -/
abbrev d₂ (B : List Byte) (t : Nat) : Nat :=
  (xofByte B (3 * t + 1)).toNat / 16 + 16 * (xofByte B (3 * t + 2)).toNat

/-- The coefficients accepted after `t` iterations. -/
abbrev LA (B : List Byte) (t : Nat) : List VG.Spec.MlKem.Zq := sampleAfter [] (xofByte B) t

/-- The registers the loop changes. -/
abbrev lRegs : List Reg := [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x11, .x12, .x13, .x14, .x15]

/-- After `t` of `N` iterations. -/
structure Inv (N : Nat) (B : List Byte) (bP aP : Addr) (s₀ : State) (t : Nat) (u : State) : Prop where
  acc : VG.Proof.MlKem.AArch64.Sample.Acc aP s₀ (VG.Proof.MlKem.AArch64.Sample.LA B t) u
  keep : Keep VG.Proof.MlKem.AArch64.Sample.lRegs s₀ u
  x2 : u.gpr .x2 = bP + BitVec.ofNat 64 (3 * t)
  x5 : (u.gpr .x5).toNat = N - t
  x10 : (u.gpr .x10).toNat = 15

theorem sampleStepCap_eq (L : List VG.Spec.MlKem.Zq) (c₀ c₁ c₂ : Byte) (hL : L.length ≠ VG.Spec.MlKem.n) :
    sampleStepCap L c₀ c₁ c₂ =
      let a := if c₀.toNat + 256 * (c₁.toNat % 16) < VG.Spec.MlKem.q
        then L ++ [ofNat (c₀.toNat + 256 * (c₁.toNat % 16))] else L
      if c₁.toNat / 16 + 16 * c₂.toNat < VG.Spec.MlKem.q ∧ a.length < VG.Spec.MlKem.n
        then a ++ [ofNat (c₁.toNat / 16 + 16 * c₂.toNat)] else a := by
  unfold sampleStepCap sampleStep
  rw [ite_eq_right hL]

theorem acc_keep {aP : Addr} {s₀ : State} {L : List VG.Spec.MlKem.Zq} {u u' : State} (h : VG.Proof.MlKem.AArch64.Sample.Acc aP s₀ L u)
    {rs : List Reg} (hk : Keep rs u u') (hm : u'.mem = u.mem) (h3 : Reg.x3 ∉ rs := by decide)
    (h4 : Reg.x4 ∉ rs := by decide) (h9 : Reg.x9 ∉ rs := by decide) : VG.Proof.MlKem.AArch64.Sample.Acc aP s₀ L u' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp], h.len, by rw [hk.get .x3 h3, h.x3],
    by rw [hk.get .x4 h4, h.x4], by rw [hk.get .x9 h9, h.x9], by rw [hm]; exact h.coeffs,
    by rw [hm]; exact h.frame⟩

/-- The candidates of chunk `t`. -/
theorem chunk_ok {N : Nat} {B : List Byte} {bP aP : Addr} {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.LPre N B bP aP s₀)
    {t : Nat} (ht : t < N) {u : State} (h : VG.Proof.MlKem.AArch64.Sample.Inv N B bP aP s₀ t u) :
    WP isa (.block sampleChunk) u fun u' => VG.Proof.MlKem.AArch64.Sample.Acc aP s₀ (VG.Proof.MlKem.AArch64.Sample.LA B t) u' ∧
      Keep [.x2, .x5, .x6, .x7, .x8, .x11, .x12, .x13] u u' ∧
      u'.gpr .x2 = bP + BitVec.ofNat 64 (3 * (t + 1)) ∧ (u'.gpr .x5).toNat = N - (t + 1) ∧
      (u'.gpr .x11).toNat = VG.Proof.MlKem.AArch64.Sample.d₁ B t ∧ (u'.gpr .x12).toNat = VG.Proof.MlKem.AArch64.Sample.d₂ B t := by
  have hin : ∀ p < 3 * N, InRegions (u.rd ++ u.wr) (bP + BitVec.ofNat 64 p) 1 := fun p hp' => by
    rw [h.acc.rd, h.acc.wr]; exact hp.inb p hp'
  have hb : ∀ p < 3 * N, (u.mem (bP + BitVec.ofNat 64 p)).toNat = (xofByte B p).toNat := fun p hp' => by
    rw [byte_frame h.acc.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.disj) (by have := hp.bound; omega) hp', hp.buf p hp']
  have a : ∀ r, u.gpr .x2 + BitVec.ofNat 64 r = bP + BitVec.ofNat 64 (3 * t + r) := fun r => by
    rw [h.x2, ptr_add]
  refine VG.Proof.MlKem.AArch64.wp_ldrb (a := bP + BitVec.ofNat 64 (3 * t + 0)) (by decide) (a 0) (hin _ (by omega))
    fun u₁ h₁ e₁ => ?_
  refine VG.Proof.MlKem.AArch64.wp_ldrb (a := bP + BitVec.ofNat 64 (3 * t + 1)) (by decide) (by rw [h₁.get .x2, a])
    (by rw [h₁.rd, h₁.wr]; exact hin _ (by omega)) fun u₂ h₂ e₂ => ?_
  refine VG.Proof.MlKem.AArch64.wp_ldrb (a := bP + BitVec.ofNat 64 (3 * t + 2)) (by decide)
    (by rw [h₂.get .x2, h₁.get .x2, a]) (by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact hin _ (by omega))
    fun u₃ h₃ e₃ => ?_
  refine VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun u₄ h₄ e₄ => VG.Proof.MlKem.AArch64.wp_subImm (by decide) fun u₅ h₅ e₅ =>
    VG.Proof.MlKem.AArch64.wp_and fun u₆ h₆ e₆ => wp_lsl (by decide) fun u₇ h₇ e₇ => VG.Proof.MlKem.AArch64.wp_add fun u₈ h₈ e₈ =>
    VG.Proof.MlKem.AArch64.wp_lsr (by decide) fun u₉ h₉ e₉ => wp_lsl (by decide) fun u₁₀ h₁₀ e₁₀ =>
    VG.Proof.MlKem.AArch64.wp_add fun u₁₁ h₁₁ e₁₁ => VG.Proof.MlKem.AArch64.wp_nil ?_
  have l0 := (xofByte B (3 * t)).isLt
  have l1 := (xofByte B (3 * t + 1)).isLt
  have l2 := (xofByte B (3 * t + 2)).isLt
  have v6 : (u₅.gpr .x6).toNat = (xofByte B (3 * t)).toNat := by
    rw [h₅.get .x6, h₄.get .x6, h₃.get .x6, h₂.get .x6, e₁, toNat_byte, Nat.add_zero, hb _ (by omega)]
  have v7 : (u₅.gpr .x7).toNat = (xofByte B (3 * t + 1)).toNat := by
    rw [h₅.get .x7, h₄.get .x7, h₃.get .x7, e₂, toNat_byte, h₁.mem, hb _ (by omega)]
  have v8 : (u₅.gpr .x8).toNat = (xofByte B (3 * t + 2)).toNat := by
    rw [h₅.get .x8, h₄.get .x8, e₃, toNat_byte, h₂.mem, h₁.mem, hb _ (by omega)]
  have k₁₁ := (((((((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans
    h₆.keep).trans h₇.keep).trans h₈.keep).trans h₉.keep).trans h₁₀.keep).trans h₁₁.keep
  have m₁₁ : u₁₁.mem = u.mem := by
    rw [h₁₁.mem, h₁₀.mem, h₉.mem, h₈.mem, h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨VG.Proof.MlKem.AArch64.Sample.acc_keep h.acc (k₁₁.mono (rs' := [.x2, .x5, .x6, .x7, .x8, .x11, .x12, .x13]) (by decide))
    m₁₁, k₁₁.mono (by decide), ?_, ?_, ?_, ?_⟩
  · rw [h₁₁.get .x2, h₁₀.get .x2, h₉.get .x2, h₈.get .x2, h₇.get .x2, h₆.get .x2, h₅.get .x2, e₄,
      h₃.get .x2, h₂.get .x2, h₁.get .x2, h.x2, ptr_add, show 3 * t + 3 = 3 * (t + 1) by omega]
  · have c5 : (u₄.gpr .x5).toNat = N - t := by
      rw [h₄.get .x5, h₃.get .x5, h₂.get .x5, h₁.get .x5, h.x5]
    rw [h₁₁.get .x5, h₁₀.get .x5, h₉.get .x5, h₈.get .x5, h₇.get .x5, h₆.get .x5, e₅,
      toNat_sub_n (by rw [c5]; simp; omega), c5]
    simp
    omega
  · have c6 : (u₆.gpr .x11).toNat = (xofByte B (3 * t + 1)).toNat % 16 := by
      rw [e₆, toNat_and_mask _ _ (k := 4) (by
        rw [h₅.get .x10, h₄.get .x10, h₃.get .x10, h₂.get .x10, h₁.get .x10, h.x10]), v7]
    have c7 : (u₇.gpr .x11).toNat = (xofByte B (3 * t + 1)).toNat % 16 * 256 := by
      rw [e₇, toNat_lsl_n (by rw [c6]; omega), c6]
    rw [h₁₁.get .x11, h₁₀.get .x11, h₉.get .x11, e₈,
      toNat_add_n (by rw [c7, h₇.get .x6, h₆.get .x6, v6]; omega), c7, h₇.get .x6, h₆.get .x6, v6]
    simp only [VG.Proof.MlKem.AArch64.Sample.d₁]
    omega
  · have c9 : (u₉.gpr .x12).toNat = (xofByte B (3 * t + 1)).toNat / 16 := by
      rw [e₉, toNat_lsr, h₈.get .x7, h₇.get .x7, h₆.get .x7, v7]
    have c10 : (u₁₀.gpr .x13).toNat = (xofByte B (3 * t + 2)).toNat * 16 := by
      rw [e₁₀, toNat_lsl_n (by rw [h₉.get .x8, h₈.get .x8, h₇.get .x8, h₆.get .x8, v8]; omega),
        h₉.get .x8, h₈.get .x8, h₇.get .x8, h₆.get .x8, v8]
    rw [e₁₁, toNat_add_n (by rw [h₁₀.get .x12, c9, c10]; omega), h₁₀.get .x12, c9, c10]
    simp only [VG.Proof.MlKem.AArch64.Sample.d₂]
    omega

/-- Whether the candidates are accepted: nothing once there are 256
coefficients. -/
theorem tail_ok {aP : Addr} {s₀ : State} (hina : ∀ i < 256, InRegions s₀.wr (coeffAddr aP i) 4)
    {L : List VG.Spec.MlKem.Zq} {u : State} (h : VG.Proof.MlKem.AArch64.Sample.Acc aP s₀ L u) {c₀ c₁ c₂ : Byte}
    (h11 : (u.gpr .x11).toNat = c₀.toNat + 256 * (c₁.toNat % 16))
    (h12 : (u.gpr .x12).toNat = c₁.toNat / 16 + 16 * c₂.toNat) :
    WP isa (.ite (.zero .x .x4) (.block [])
      (.seq (.block (sampleAccept .x11)) (.ite (.zero .x .x4) (.block [])
        (.block (sampleAccept .x12))))) u
      fun u' => VG.Proof.MlKem.AArch64.Sample.Acc aP s₀ (sampleStepCap L c₀ c₁ c₂) u' ∧ Keep [.x3, .x4, .x13, .x14, .x15] u u' := by
  have l0 := c₀.isLt
  have l1 := c₁.isLt
  have l2 := c₂.isLt
  have hn : VG.Spec.MlKem.n = 256 := rfl
  have hL := h.len
  refine WP.ite (u.gpr .x4 == 0) (VG.Proof.MlKem.AArch64.eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
  · rw [eq_zero_iff, decide_eq_true_eq, h.x4] at hz
    rw [sampleStepCap_full (by omega)]
    exact VG.Proof.MlKem.AArch64.wp_nil ⟨h, Keep.refl _ _⟩
  rw [eq_zero_iff, decide_eq_false_iff_not, h.x4] at hz
  rw [VG.Proof.MlKem.AArch64.Sample.sampleStepCap_eq L c₀ c₁ c₂ (by omega)]
  refine WP.seq (WP.mono (VG.Proof.MlKem.AArch64.Sample.accept_ok hina h (by omega) (d := .x11) (by decide) h11 (by omega))
    fun u₂ ⟨a₂, k₂⟩ => ?_)
  have hl1 := a₂.len
  refine WP.ite (u₂.gpr .x4 == 0) (VG.Proof.MlKem.AArch64.eval_zero _ _) (fun hz' => ?_) (fun hz' => ?_)
  · rw [eq_zero_iff, decide_eq_true_eq, a₂.x4] at hz'
    dsimp only
    rw [ite_eq_right (fun hc => by omega)]
    exact VG.Proof.MlKem.AArch64.wp_nil ⟨a₂, k₂⟩
  · rw [eq_zero_iff, decide_eq_false_iff_not, a₂.x4] at hz'
    refine WP.mono (VG.Proof.MlKem.AArch64.Sample.accept_ok hina a₂ (by omega) (d := .x12) (v := c₁.toNat / 16 + 16 * c₂.toNat)
      (by decide)
      (by rw [k₂.get .x12]; exact h12) (by omega)) fun u₃ ⟨a₃, k₃⟩ => ⟨?_, (k₂.trans k₃).mono⟩
    dsimp only
    by_cases hd : c₁.toNat / 16 + 16 * c₂.toNat < VG.Spec.MlKem.q
    · rw [ite_eq_left ⟨hd, by omega⟩]; rw [ite_eq_left hd] at a₃; exact a₃
    · rw [ite_eq_right (fun hc => hd hc.1)]; rw [ite_eq_right hd] at a₃; exact a₃

/-- One iteration. -/
theorem body_ok {N : Nat} {B : List Byte} {bP aP : Addr} {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.LPre N B bP aP s₀)
    {t : Nat} (ht : t < N) {u : State} (h : VG.Proof.MlKem.AArch64.Sample.Inv N B bP aP s₀ t u) :
    WP isa sampleBody u fun u' =>
      VG.Proof.MlKem.AArch64.Sample.Inv N B bP aP s₀ (t + 1) u' ∧ ((u'.gpr .x5).toNat ≠ 0 ↔ t + 1 ≠ N) := by
  refine WP.seq (WP.mono (VG.Proof.MlKem.AArch64.Sample.chunk_ok hp ht h) fun u₁ ⟨a₁, k₁, x2₁, x5₁, x11₁, x12₁⟩ =>
    WP.mono (VG.Proof.MlKem.AArch64.Sample.tail_ok hp.ina a₁ x11₁ x12₁) fun u' ⟨a', k'⟩ => ?_)
  have x5' : (u'.gpr .x5).toNat = N - (t + 1) := by rw [k'.get .x5, x5₁]
  refine ⟨⟨a', ((h.keep.trans k₁).trans k').mono (by decide), by rw [k'.get .x2, x2₁], x5',
    by rw [k'.get .x10, k₁.get .x10, h.x10]⟩, by rw [x5']; omega⟩

/-! ## The loop -/

theorem cv_toPoly {L : List VG.Spec.MlKem.Zq} {i : Nat} (hi : i < 256) :
    VG.Proof.MlKem.AArch64.Sample.cv L i = BitVec.ofNat 32 ((toPoly L)[i]!).val := by
  simp [VG.Proof.MlKem.AArch64.Sample.cv, toPoly, hi]

/-- The loop's result: 1 and `SampleNTT` at `a`, or 0 and failure; `a` is
reduced either way. -/
def Res (B : List Byte) (aP : Addr) (u : State) : Prop :=
  Reduced u.mem aP ∧ ((u.gpr .x0 = 1 ∧ PolyIs u.mem aP (toPoly (VG.Proof.MlKem.AArch64.Sample.LA B 280)) ∧
      sampleNTT 280 B = some (toPoly (VG.Proof.MlKem.AArch64.Sample.LA B 280))) ∨
    (u.gpr .x0 = 0 ∧ sampleNTT 280 B = none))

theorem reduced_of_coeffs {m : Mem} {p : Addr} {L : List VG.Spec.MlKem.Zq} (h : CoeffsUpTo m p L.length (VG.Proof.MlKem.AArch64.Sample.cv L) fun _ => 0) :
    Reduced m p := fun i hi => by
  rw [h i hi]
  split
  · simp only [VG.Proof.MlKem.AArch64.Sample.cv, BitVec.toNat_ofNat]
    have := val_lt (L.getD i 0)
    have hq : VG.Spec.MlKem.q = 3329 := rfl
    omega
  · show (0 : BitVec 32).toNat < VG.Spec.MlKem.q
    decide

/-- The `N` iterations. -/
theorem iters_ok {N : Nat} (hN : 0 < N) {B : List Byte} {bP aP : Addr} {s₀ : State}
    (hp : VG.Proof.MlKem.AArch64.Sample.LPre N B bP aP s₀) :
    WP isa (.loop sampleBody (.nonzero .x .x5)) s₀ (VG.Proof.MlKem.AArch64.Sample.Inv N B bP aP s₀ N) := by
  have l0 : (VG.Proof.MlKem.AArch64.Sample.LA B 0).length = 0 := rfl
  have i₀ : VG.Proof.MlKem.AArch64.Sample.Inv N B bP aP s₀ 0 s₀ := by
    refine ⟨⟨rfl, rfl, rfl, by rw [l0]; omega, by rw [hp.x3, l0, coeffAddr, Nat.mul_zero, ptr_zero],
      by rw [hp.x4, l0], hp.x9, fun i hi _ => ?_, Frame.refl _ _⟩, Keep.refl _ _,
      by rw [hp.x2, Nat.mul_zero, ptr_zero], by rw [hp.x5, Nat.sub_zero], hp.x10⟩
    rw [hp.zero i hi, l0, ite_eq_right (Nat.not_lt_zero i)]
  exact count_loop hN (VG.Proof.MlKem.AArch64.Sample.Inv N B bP aP s₀) (fun t ht u h => VG.Proof.MlKem.AArch64.Sample.body_ok hp ht h) i₀

/-- Coefficient `j`, which may hold a rejected candidate, set to zero if
there are fewer than 256. -/
theorem fix_ok {aP : Addr} {s₀ : State} (hina : ∀ i < 256, InRegions s₀.wr (coeffAddr aP i) 4)
    {L : List VG.Spec.MlKem.Zq} {u : State} (h : VG.Proof.MlKem.AArch64.Sample.Acc aP s₀ L u) :
    WP isa (.ite (.zero .x .x4) (.block []) (.block [.movz .x .x13 0 0, .str .w .x13 .x3 0])) u
      fun u' => Keep [.x13] u u' ∧ VG.Frame [polyRegion aP] s₀.mem u'.mem ∧ Reduced u'.mem aP ∧
        (L.length = 256 → CoeffsUpTo u'.mem aP L.length (VG.Proof.MlKem.AArch64.Sample.cv L) fun _ => 0) := by
  have hL := h.len
  refine WP.ite (u.gpr .x4 == 0) (VG.Proof.MlKem.AArch64.eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
  · rw [eq_zero_iff, decide_eq_true_eq, h.x4] at hz
    have hc := h.coeffs.full (by omega)
    exact VG.Proof.MlKem.AArch64.wp_nil ⟨Keep.refl _ _, h.frame, VG.Proof.MlKem.AArch64.Sample.reduced_of_coeffs hc, fun _ => hc⟩
  · rw [eq_zero_iff, decide_eq_false_iff_not, h.x4] at hz
    have hlt : L.length < 256 := by omega
    refine VG.Proof.MlKem.AArch64.wp_movz fun u₁ h₁ e₁ => wp_strw (a := coeffAddr aP L.length) (by decide)
      (by rw [h₁.gpr .x3 (by decide), h.x3, ptr_zero]) (by rw [h₁.wr, h.wr]; exact hina _ hlt)
      fun u₂ h₂ => VG.Proof.MlKem.AArch64.wp_nil ?_
    have m₂ : u₂.mem = u.mem.writeW (coeffAddr aP L.length) (0 : BitVec 32) := by
      rw [h₂.mem, e₁, h₁.mem]
      rfl
    refine ⟨(h₁.keep.trans h₂.keep).mono (by decide), ?_, ?_, fun hf => absurd hf (by omega)⟩
    · rw [m₂]
      exact h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ (show L.length < VG.Spec.MlKem.n from hlt))
    · rw [m₂]
      exact VG.Proof.MlKem.AArch64.Sample.reduced_of_coeffs (h.coeffs.zero hlt)

theorem loop_ok {B : List Byte} {bP aP : Addr} {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.LPre 280 B bP aP s₀) :
    WP isa sampleLoop s₀ fun u => Keep (.x0 :: VG.Proof.MlKem.AArch64.Sample.lRegs) s₀ u ∧ VG.Frame [polyRegion aP] s₀.mem u.mem ∧
      VG.Proof.MlKem.AArch64.Sample.Res B aP u := by
  refine WP.seq (WP.mono (VG.Proof.MlKem.AArch64.Sample.iters_ok (by decide) hp) fun u h =>
    WP.seq (WP.mono (VG.Proof.MlKem.AArch64.Sample.fix_ok hp.ina h.acc) fun u' ⟨k', fr', red', full'⟩ => ?_))
  refine VG.Proof.MlKem.AArch64.wp_subImm (by decide) fun u₁ h₁ e₁ => VG.Proof.MlKem.AArch64.wp_lsr (by decide) fun u₂ h₂ e₂ => VG.Proof.MlKem.AArch64.wp_nil ?_
  have hL := h.acc.len
  have c4 : (u'.gpr .x4).toNat = 256 - (VG.Proof.MlKem.AArch64.Sample.LA B 280).length := by rw [k'.get .x4, h.acc.x4]
  refine ⟨((h.keep.trans (k'.trans (h₁.keep.trans h₂.keep)))).mono (by decide), by
    rw [h₂.mem, h₁.mem]; exact fr', ?_⟩
  have v0 : (u₂.gpr .x0).toNat = if (VG.Proof.MlKem.AArch64.Sample.LA B 280).length = 256 then 1 else 0 := by
    rw [e₂, toNat_lsr, e₁, BitVec.toNat_sub, c4]
    simp only [BitVec.toNat_ofNat]
    split <;> omega
  refine ⟨by rw [h₂.mem, h₁.mem]; exact red', ?_⟩
  by_cases hf : (VG.Proof.MlKem.AArch64.Sample.LA B 280).length = 256
  · rw [ite_eq_left hf] at v0
    refine .inl ⟨BitVec.eq_of_toNat_eq (by rw [v0]; rfl), ?_, sampleNTT_of_full (Nat.le_refl _) hf⟩
    rw [h₂.mem, h₁.mem]
    have hc := full' hf
    rw [hf] at hc
    exact CoeffsUpTo.polyIs hc fun i hi => VG.Proof.MlKem.AArch64.Sample.cv_toPoly hi
  · rw [ite_eq_right hf] at v0
    exact .inr ⟨BitVec.eq_of_toNat_eq (by rw [v0]; rfl), sampleNTT_none hf⟩

end VG.Proof.MlKem.AArch64.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.SampleSqueeze`. -/
section

/-!
# ML-KEM on AArch64: `SampleNTT` up to its loop

`sampleSqueezeN len setup` saves our caller's `x25`, `x26`, `x30` and `x24` in
`scratch`, computes `len` bytes of SHAKE128 of the seed into `scratch[0, len)`
with the verified Keccak functions from the all-zero state
(`Proof/MlKem/KPke.lean`), sets `a` to zeros, and sets up the loop: it leaves
what the loop needs (`LPre`), and either the registers restored
(`sampleSqueeze`, `rest_ok`) or still saved (`sampleFast`'s, `restN_ok`).
-/

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- AArch64 contract for `sampleNTT(seed = x0, a = x1, scratch = x2) -> w0`:
with the 34 bytes `B` at `seed`, writes `SampleNTT(B)` to `a` and returns 1,
or returns 0. The code may read `seed`, and write `a` and `scratch` (2048
bytes), and the 16 bytes below the stack pointer (the Keccak functions'
frames). It may leak `B`. -/
def sampleAArch64 : Contract AArch64.isa where
  pre s :=
    let seed : Region := ⟨s.gpr .x0, 34⟩
    let a : Region := ⟨s.gpr .x1, 1024⟩
    let scratch : Region := ⟨s.gpr .x2, 2048⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [seed] ∧ s.wr = [a, scratch] ∧ seed.Disjoint a ∧ seed.Disjoint scratch ∧
    a.Disjoint scratch ∧ 16 ≤ s.sp.toNat ∧ stack.Disjoint seed ∧ stack.Disjoint a ∧
    stack.Disjoint scratch
  post s s' :=
    ((s'.gpr .x0).setWidth 32 = 1 → Reduced s'.mem (s.gpr .x1)) ∧
      Outcome (fun iters => sampleNTT iters (bytesAt s.mem (s.gpr .x0) 34))
        ((s'.gpr .x0).setWidth 32) (polyAt s'.mem (s.gpr .x1))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.sp = s₂.sp ∧
      (bytesAt s₁.mem (s₁.gpr .x0) 34).map (·.toNat) = (bytesAt s₂.mem (s₂.gpr .x0) 34).map (·.toNat)

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Sample

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr shakeSuffix)

section
variable (s₀ : State)

abbrev sdP : Addr := s₀.gpr .x0
abbrev aP : Addr := s₀.gpr .x1
abbrev scP : Addr := s₀.gpr .x2
/-- Offset `k` of `scratch`. -/
abbrev So (k : Nat) : Addr := VG.Proof.MlKem.AArch64.Sample.scP s₀ + BitVec.ofNat 64 k
abbrev seedR : Region := ⟨VG.Proof.MlKem.AArch64.Sample.sdP s₀, 34⟩
abbrev aR : Region := polyRegion (VG.Proof.MlKem.AArch64.Sample.aP s₀)
abbrev scR : Region := ⟨VG.Proof.MlKem.AArch64.Sample.scP s₀, 2048⟩
abbrev kR : Region := ⟨s₀.sp - 16, 16⟩
/-- The seed. -/
abbrev Bs : List Byte := bytesAt s₀.mem (VG.Proof.MlKem.AArch64.Sample.sdP s₀) 34

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.MlKem.AArch64.Sample.seedR s₀]
  wr : s₀.wr = [VG.Proof.MlKem.AArch64.Sample.aR s₀, VG.Proof.MlKem.AArch64.Sample.scR s₀]
  d_sa : (VG.Proof.MlKem.AArch64.Sample.seedR s₀).Disjoint (VG.Proof.MlKem.AArch64.Sample.aR s₀)
  d_ss : (VG.Proof.MlKem.AArch64.Sample.seedR s₀).Disjoint (VG.Proof.MlKem.AArch64.Sample.scR s₀)
  d_as : (VG.Proof.MlKem.AArch64.Sample.aR s₀).Disjoint (VG.Proof.MlKem.AArch64.Sample.scR s₀)
  sp16 : 16 ≤ s₀.sp.toNat
  k_s : (VG.Proof.MlKem.AArch64.Sample.kR s₀).Disjoint (VG.Proof.MlKem.AArch64.Sample.seedR s₀)
  k_a : (VG.Proof.MlKem.AArch64.Sample.kR s₀).Disjoint (VG.Proof.MlKem.AArch64.Sample.aR s₀)
  k_c : (VG.Proof.MlKem.AArch64.Sample.kR s₀).Disjoint (VG.Proof.MlKem.AArch64.Sample.scR s₀)

theorem pre_of {s₀ : State} (h : sampleAArch64.pre s₀) : VG.Proof.MlKem.AArch64.Sample.Pre s₀ :=
  let ⟨a, b, c, d, e, f, g, i, j⟩ := h
  ⟨a, b, c, d, e, f, g, i, j⟩

theorem mem2 {α : Type} {a b x : α} (h : x ∈ [a, b]) : x = a ∨ x = b := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (List.mem_singleton.mp h)

theorem mem3 {α : Type} {a b c x : α} (h : x ∈ [a, b, c]) : x = a ∨ x = b ∨ x = c := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (VG.Proof.MlKem.AArch64.Sample.mem2 h)

theorem mem4 {α : Type} {a b c d x : α} (h : x ∈ [a, b, c, d]) : x = a ∨ x = b ∨ x = c ∨ x = d := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (VG.Proof.MlKem.AArch64.Sample.mem3 h)

/-! ## Regions -/

theorem below16 (sp : Addr) : below sp 16 = ⟨sp - 16, 16⟩ := rfl

theorem sub_so (s₀ : State) {off n : Nat} (h : off + n ≤ 2048) :
    Region.Sub ⟨VG.Proof.MlKem.AArch64.Sample.So s₀ off, n⟩ (VG.Proof.MlKem.AArch64.Sample.scR s₀) := by
  intro x hx
  simp only [Region.Contains] at *
  have : (x - VG.Proof.MlKem.AArch64.Sample.scP s₀).toNat ≤ (x - VG.Proof.MlKem.AArch64.Sample.So s₀ off).toNat + off := by
    rw [show x - VG.Proof.MlKem.AArch64.Sample.scP s₀ = (x - VG.Proof.MlKem.AArch64.Sample.So s₀ off) + BitVec.ofNat 64 off by bv_omega, BitVec.toNat_add,
      BitVec.toNat_ofNat]
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.add_le_add_left (Nat.mod_le _ _) _)
  omega

theorem disj_so (s₀ : State) {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a + n ≤ 2048)
    (hb : b + k ≤ 2048) : Region.Disjoint ⟨VG.Proof.MlKem.AArch64.Sample.So s₀ a, n⟩ ⟨VG.Proof.MlKem.AArch64.Sample.So s₀ b, k⟩ := fun x h₁ h₂ =>
  sep_off (VG.Proof.MlKem.AArch64.Sample.scP s₀) h (by omega) (by omega) x (Nat.lt_of_succ_le h₁) (Nat.lt_of_succ_le h₂)

theorem in_sc {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) {off n : Nat} (h : off + n ≤ 2048) :
    InRegions s₀.wr (VG.Proof.MlKem.AArch64.Sample.So s₀ off) n := by
  rw [hp.wr]; exact in_regions (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    (contains_off h (by decide))

theorem covers_sc {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ off, r.base = VG.Proof.MlKem.AArch64.Sample.So s₀ off ∧ off + r.len ≤ 2048) : Covers rs s₀.wr :=
  Covers.of_sub fun r hr => by
    obtain ⟨off, hb, hl⟩ := h r hr
    exact ⟨VG.Proof.MlKem.AArch64.Sample.scR s₀, by rw [hp.wr]; simp, off, hb, hl⟩

theorem covers_rw {s₀ : State} {rs : List Region} (h : Covers rs s₀.wr) :
    Covers rs (s₀.rd ++ s₀.wr) := fun a n hi => in_rd_wr (h a n hi)

/-- The stack is disjoint from the parts of `scratch`. -/
theorem k_so {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) {off n : Nat} (h : off + n ≤ 2048) :
    (VG.Proof.MlKem.AArch64.Sample.kR s₀).Disjoint ⟨VG.Proof.MlKem.AArch64.Sample.So s₀ off, n⟩ := hp.k_c.sub_right (VG.Proof.MlKem.AArch64.Sample.sub_so s₀ h)

/-! ## The saved registers -/

/-- Our caller's `x25`, `x26`, `x30` and `x24`, saved in `scratch`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  m.readW (VG.Proof.MlKem.AArch64.Sample.So s₀ 1680) 64 = s₀.gpr .x25 ∧ m.readW (VG.Proof.MlKem.AArch64.Sample.So s₀ 1688) 64 = s₀.gpr .x26 ∧
    m.readW (VG.Proof.MlKem.AArch64.Sample.So s₀ 1696) 64 = s₀.gpr .x30 ∧ m.readW (VG.Proof.MlKem.AArch64.Sample.So s₀ 1704) 64 = s₀.gpr .x24

theorem Saved.frame {s₀ : State} {m m' : Mem} (h : VG.Proof.MlKem.AArch64.Sample.Saved s₀ m) {rs : List Region} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨VG.Proof.MlKem.AArch64.Sample.So s₀ 1680, 32⟩ r) : VG.Proof.MlKem.AArch64.Sample.Saved s₀ m' := by
  have e : ∀ k, k < 4 → m'.readW (VG.Proof.MlKem.AArch64.Sample.So s₀ (1680 + 8 * k)) 64 = m.readW (VG.Proof.MlKem.AArch64.Sample.So s₀ (1680 + 8 * k)) 64 :=
    fun k hk => by
      refine hf.readW (r := ⟨VG.Proof.MlKem.AArch64.Sample.So s₀ 1680, 32⟩) ?_ hd (by decide)
      rw [show VG.Proof.MlKem.AArch64.Sample.So s₀ (1680 + 8 * k) = VG.Proof.MlKem.AArch64.Sample.So s₀ 1680 + BitVec.ofNat 64 (8 * k) by rw [ptr_add]]
      exact contains_off (by omega) (by decide)
  exact ⟨(e 0 (by decide)).trans h.1, (e 1 (by decide)).trans h.2.1, (e 2 (by decide)).trans h.2.2.1,
    (e 3 (by decide)).trans h.2.2.2⟩

/-- Between the prologue and the loop: `x24 = seed`, `x25 = a` and
`x26 = scratch`, the saved registers, the other callee-saved registers,
and the memory outside `scratch` and the stack below it. -/
structure Mid (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x24 : s.gpr .x24 = VG.Proof.MlKem.AArch64.Sample.sdP s₀
  x25 : s.gpr .x25 = VG.Proof.MlKem.AArch64.Sample.aP s₀
  x26 : s.gpr .x26 = VG.Proof.MlKem.AArch64.Sample.scP s₀
  cs : ∀ r ∈ preserved, r ≠ .x24 → r ≠ .x25 → r ≠ .x26 → r ≠ .x30 → s.gpr r = s₀.gpr r
  sv : VG.Proof.MlKem.AArch64.Sample.Saved s₀ s.mem
  frame : Frame [VG.Proof.MlKem.AArch64.Sample.scR s₀, below s₀.sp 16] s₀.mem s.mem
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64

theorem preserved_ne : ∀ r ∈ preserved, r ≠ .x30 → r ∉ linkRegs := by decide

/-- A call that writes parts of `scratch` apart from the saved registers,
and the stack below it. -/
theorem Mid.call {s₀ s s' : State} (h : VG.Proof.MlKem.AArch64.Sample.Mid s₀ s) {rs : List Region} (hk : VG.Proof.MlKem.AArch64.Kept rs s s')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨VG.Proof.MlKem.AArch64.Sample.So s₀ 1680, 32⟩ r)
    (hs : ∀ r ∈ rs, ∃ r' ∈ [VG.Proof.MlKem.AArch64.Sample.scR s₀, below s₀.sp 16], Region.Sub r r') : VG.Proof.MlKem.AArch64.Sample.Mid s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    by rw [hk.cs _ (by decide) (by decide), h.x24],
    by rw [hk.cs _ (by decide) (by decide), h.x25], by rw [hk.cs _ (by decide) (by decide), h.x26],
    fun r hr h24 h25 h26 h30 => by rw [hk.cs r hr h30, h.cs r hr h24 h25 h26 h30],
    h.sv.frame hk.frame hd, h.frame.trans (hk.frame.sub hs), fun r hr => (hk.vcs r hr).trans (h.vcs r hr)⟩

/-- A block that writes no callee-saved register nor memory. -/
theorem Mid.keep {s₀ s s' : State} (h : VG.Proof.MlKem.AArch64.Sample.Mid s₀ s) {regs : List Reg}
    (hk : Keep regs s s') (hm : s'.mem = s.mem) (hr : ∀ r ∈ regs, r ∉ preserved := by decide) :
    VG.Proof.MlKem.AArch64.Sample.Mid s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    by rw [hk.get .x24 (fun h' => hr _ h' (by decide)), h.x24],
    by rw [hk.get .x25 (fun h' => hr _ h' (by decide)), h.x25],
    by rw [hk.get .x26 (fun h' => hr _ h' (by decide)), h.x26],
    fun r hp' h24 h25 h26 h30 => by
      rw [hk.get r (fun h' => hr _ h' hp'), h.cs r hp' h24 h25 h26 h30],
    by rw [hm]; exact h.sv, by rw [hm]; exact h.frame, fun r hr => (hk.vcs r hr).trans (h.vcs r hr)⟩

/-! ## The prologue -/

/-- The zeros of the Keccak state. -/
def zst (n : Nat) : List Instr := (List.range n).map fun k => .str .x .x9 .x2 (840 + 8 * k)

theorem zst_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) :
    ∀ n ≤ 25, ∀ {s : State}, s.gpr .x9 = 0 → s.gpr .x2 = VG.Proof.MlKem.AArch64.Sample.scP s₀ → s.wr = s₀.wr →
      WP isa (.block (VG.Proof.MlKem.AArch64.Sample.zst n)) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp ∧ (∀ k < n, s'.mem.readW (VG.Proof.MlKem.AArch64.Sample.So s₀ (840 + 8 * k)) 64 = 0) ∧
        Frame [⟨VG.Proof.MlKem.AArch64.Sample.So s₀ 840, 200⟩] s.mem s'.mem
  | 0, _, s, _, _, _ => wp_nil ⟨rfl, rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _),
      Frame.refl _ _⟩
  | n + 1, hn, s, h9, h2, hw => by
    rw [VG.Proof.MlKem.AArch64.Sample.zst, List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (VG.Proof.MlKem.AArch64.Sample.zst_ok hp n (by omega) h9 h2 hw) fun s₁ ⟨g₁, r₁, w₁, p₁, z₁, f₁⟩ => ?_
    refine wp_strx (a := VG.Proof.MlKem.AArch64.Sample.So s₀ (840 + 8 * n)) (by constructor <;> omega) (by rw [g₁, h2])
      (by rw [w₁, hw]; exact VG.Proof.MlKem.AArch64.Sample.in_sc hp (by omega)) fun s₂ h₂ => wp_nil ?_
    refine ⟨by rw [h₂.gpr, g₁], by rw [h₂.rd, r₁], by rw [h₂.wr, w₁], by rw [h₂.sp, p₁],
      fun k hk => ?_, ?_⟩
    · rw [h₂.mem, g₁, h9]
      by_cases e : k = n
      · subst e; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (sep_off _ (by omega) (by omega) (by omega)) (by decide)]
        exact z₁ k (by omega)
    · rw [h₂.mem]
      refine f₁.writeW (List.mem_singleton_self _) _ ?_
      rw [show VG.Proof.MlKem.AArch64.Sample.So s₀ (840 + 8 * n) = VG.Proof.MlKem.AArch64.Sample.So s₀ 840 + BitVec.ofNat 64 (8 * n) by rw [ptr_add]]
      exact contains_off (by omega) (by decide)

theorem stateAt_zero {m : Mem} {p : Addr}
    (h : ∀ k < 25, m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = 0) : stateAt m p = Spec.Sha3.zero := by
  refine Vector.ext fun i hi => ?_
  simp only [stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
  exact h i hi

/-- What the prologue leaves: `absorb`'s arguments, and the Keccak state zero. -/
structure AfterPro (s₀ s : State) : Prop where
  mid : VG.Proof.MlKem.AArch64.Sample.Mid s₀ s
  zero : stateAt s.mem (VG.Proof.MlKem.AArch64.Sample.So s₀ 840) = Spec.Sha3.zero
  x0 : s.gpr .x0 = VG.Proof.MlKem.AArch64.Sample.So s₀ 840
  x1 : (s.gpr .x1).toNat = 168
  x2 : (s.gpr .x2).toNat = 0
  x3 : s.gpr .x3 = VG.Proof.MlKem.AArch64.Sample.sdP s₀
  x4 : (s.gpr .x4).toNat = 34
  x5 : s.gpr .x5 = VG.Proof.MlKem.AArch64.Sample.So s₀ 1040

theorem prologue_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) : WP isa (.block samplePrologue) s₀ (VG.Proof.MlKem.AArch64.Sample.AfterPro s₀) := by
  rw [samplePrologue, WP.block_append_iff, WP.block_append_iff]
  refine wp_strx (a := VG.Proof.MlKem.AArch64.Sample.So s₀ 1680) (by decide) rfl (VG.Proof.MlKem.AArch64.Sample.in_sc hp (by decide)) fun s₁ h₁ => ?_
  refine wp_strx (a := VG.Proof.MlKem.AArch64.Sample.So s₀ 1688) (by decide) (by rw [h₁.gpr]) (by rw [h₁.wr]; exact VG.Proof.MlKem.AArch64.Sample.in_sc hp (by decide))
    fun s₂ h₂ => ?_
  refine wp_strx (a := VG.Proof.MlKem.AArch64.Sample.So s₀ 1696) (by decide) (by rw [h₂.gpr, h₁.gpr])
    (by rw [h₂.wr, h₁.wr]; exact VG.Proof.MlKem.AArch64.Sample.in_sc hp (by decide)) fun s₃ h₃ => ?_
  refine wp_strx (a := VG.Proof.MlKem.AArch64.Sample.So s₀ 1704) (by decide) (by rw [h₃.gpr, h₂.gpr, h₁.gpr])
    (by rw [h₃.wr, h₂.wr, h₁.wr]; exact VG.Proof.MlKem.AArch64.Sample.in_sc hp (by decide)) fun s₄ h₄ => ?_
  refine wp_mov fun s₅ h₅ e₅ => wp_mov fun s₆ h₆ e₆ => wp_mov fun s₇ h₇ e₇ =>
    wp_movz fun s₈ h₈ e₈ => wp_nil ?_
  have k₈ := ((h₅.keep.trans h₆.keep).trans h₇.keep).trans h₈.keep
  have m₈ : s₈.mem = (((s₀.mem.writeW (VG.Proof.MlKem.AArch64.Sample.So s₀ 1680) (s₀.gpr .x25)).writeW (VG.Proof.MlKem.AArch64.Sample.So s₀ 1688)
      (s₀.gpr .x26)).writeW (VG.Proof.MlKem.AArch64.Sample.So s₀ 1696) (s₀.gpr .x30)).writeW (VG.Proof.MlKem.AArch64.Sample.So s₀ 1704) (s₀.gpr .x24) := by
    rw [h₈.mem, h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem, h₃.gpr, h₂.gpr, h₁.gpr]
  have g₄ : ∀ r, s₄.gpr r = s₀.gpr r := fun r => by rw [h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr]
  have sv₈ : VG.Proof.MlKem.AArch64.Sample.Saved s₀ s₈.mem := by
    rw [m₈]
    refine ⟨?_, ?_, ?_, Mem.readW_writeW_self64 _ _ _⟩
    · rw [Mem.readW_writeW_sep (sep_off _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep_off _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep_off _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep (sep_off _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep_off _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep (sep_off _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self64]
  have f₈ : Frame [VG.Proof.MlKem.AArch64.Sample.scR s₀, below s₀.sp 16] s₀.mem s₈.mem := by
    rw [m₈]
    have hm : VG.Proof.MlKem.AArch64.Sample.scR s₀ ∈ [VG.Proof.MlKem.AArch64.Sample.scR s₀, below s₀.sp 16] := List.mem_cons_self ..
    exact ((((Frame.refl _ _).writeW hm _ (contains_off (by decide) (by decide))).writeW hm _
      (contains_off (by decide) (by decide))).writeW hm _ (contains_off (by decide) (by decide))).writeW
      hm _ (contains_off (by decide) (by decide))
  have mid₈ : VG.Proof.MlKem.AArch64.Sample.Mid s₀ s₈ :=
    ⟨by rw [k₈.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd], by rw [k₈.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr],
      by rw [k₈.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp], by rw [h₈.get .x24, h₇.get .x24, h₆.get .x24, e₅, g₄],
      by rw [h₈.get .x25, h₇.get .x25, e₆, h₅.get .x1, g₄],
      by rw [h₈.get .x26, e₇, h₆.get .x2, h₅.get .x2, g₄],
      fun r hr h24 h25 h26 _ => by
        rw [h₈.get r (by simpa using fun e => by subst e; revert hr; decide),
          h₇.get r (by simpa using h26), h₆.get r (by simpa using h25), h₅.get r (by simpa using h24), g₄],
      sv₈, f₈, fun r hr => by rw [k₈.vcs r hr, h₄.vcs r hr, h₃.vcs r hr, h₂.vcs r hr, h₁.vcs r hr]⟩
  have z9 : s₈.gpr .x9 = 0 := by rw [e₈]; rfl
  have c2 : s₈.gpr .x2 = VG.Proof.MlKem.AArch64.Sample.scP s₀ := by rw [h₈.get .x2, h₇.get .x2, h₆.get .x2, h₅.get .x2, g₄]
  refine WP.mono (WP.preservedV (VG.Proof.MlKem.AArch64.Sample.zst_ok hp 25 (by decide) z9 c2 mid₈.wr) (hc := by lit_decide)) fun s₉ ⟨⟨g₉, r₉, w₉, p₉, z₉, f₉⟩, vc₉⟩ => ?_
  have mid₉ : VG.Proof.MlKem.AArch64.Sample.Mid s₀ s₉ :=
    ⟨by rw [r₉, mid₈.rd], by rw [w₉, mid₈.wr], by rw [p₉, mid₈.sp], by rw [g₉, mid₈.x24],
      by rw [g₉, mid₈.x25], by rw [g₉, mid₈.x26], fun r hr a b c d => by rw [g₉, mid₈.cs r hr a b c d],
      mid₈.sv.frame f₉ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.MlKem.AArch64.Sample.disj_so s₀ (by omega) (by omega) (by omega)),
      mid₈.frame.trans (f₉.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨VG.Proof.MlKem.AArch64.Sample.scR s₀, List.mem_cons_self .., VG.Proof.MlKem.AArch64.Sample.sub_so s₀ (by omega)⟩),
      fun r hr => (vc₉ r hr).trans (mid₈.vcs r hr)⟩
  have z₉' : stateAt s₉.mem (VG.Proof.MlKem.AArch64.Sample.So s₀ 840) = Spec.Sha3.zero :=
    VG.Proof.MlKem.AArch64.Sample.stateAt_zero fun k hk => by rw [ptr_add]; exact z₉ k hk
  refine wp_mov fun s₁₀ h₁₀ e₁₀ => wp_addImm (by decide) fun s₁₁ h₁₁ e₁₁ => wp_movz fun s₁₂ h₁₂ e₁₂ =>
    wp_movz fun s₁₃ h₁₃ e₁₃ => wp_movz fun s₁₄ h₁₄ e₁₄ => wp_addImm (by decide) fun s₁₅ h₁₅ e₁₅ =>
    wp_nil ?_
  have k₁₅ := ((((h₁₀.keep.trans h₁₁.keep).trans h₁₂.keep).trans h₁₃.keep).trans h₁₄.keep).trans h₁₅.keep
  have m₁₅ : s₁₅.mem = s₉.mem := by
    rw [h₁₅.mem, h₁₄.mem, h₁₃.mem, h₁₂.mem, h₁₁.mem, h₁₀.mem]
  refine ⟨mid₉.keep k₁₅ m₁₅, by rw [m₁₅]; exact z₉', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h₁₅.get .x0, h₁₄.get .x0, h₁₃.get .x0, h₁₂.get .x0, e₁₁, h₁₀.get .x26, mid₉.x26]
  · rw [h₁₅.get .x1, h₁₄.get .x1, h₁₃.get .x1, e₁₂]; rfl
  · rw [h₁₅.get .x2, h₁₄.get .x2, e₁₃]; rfl
  · rw [h₁₅.get .x3, h₁₄.get .x3, h₁₃.get .x3, h₁₂.get .x3, h₁₁.get .x3, e₁₀, g₉, h₈.get .x0,
      h₇.get .x0, h₆.get .x0, h₅.get .x0, g₄]
  · rw [h₁₅.get .x4, e₁₄]; rfl
  · rw [e₁₅, h₁₄.get .x26, h₁₃.get .x26, h₁₂.get .x26, h₁₁.get .x26, h₁₀.get .x26, mid₉.x26]

/-! ## The hash -/

/-- The first `len` bytes of the SHAKE128 output of the seed in `scratch`. -/
def Buf (len : Nat) (s₀ : State) (m : Mem) : Prop :=
  ∀ p < len, m (VG.Proof.MlKem.AArch64.Sample.So s₀ 0 + BitVec.ofNat 64 p) = xofByte (VG.Proof.MlKem.AArch64.Sample.Bs s₀) p

/-- The saved registers are apart from the parts of `scratch` the calls use. -/
theorem sv_disj (s₀ : State) {off n : Nat} (h : off + n ≤ 1680) :
    Region.Disjoint ⟨VG.Proof.MlKem.AArch64.Sample.So s₀ 1680, 32⟩ ⟨VG.Proof.MlKem.AArch64.Sample.So s₀ off, n⟩ := VG.Proof.MlKem.AArch64.Sample.disj_so s₀ (by omega) (by omega) (by omega)

theorem sv_below {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) : Region.Disjoint ⟨VG.Proof.MlKem.AArch64.Sample.So s₀ 1680, 32⟩ (below s₀.sp 16) := by
  rw [VG.Proof.MlKem.AArch64.Sample.below16]; exact (VG.Proof.MlKem.AArch64.Sample.k_so hp (by omega)).symm

theorem stk_eq {s₀ s : State} (h : s.sp = s₀.sp) : VG.Proof.MlKem.AArch64.stk s = VG.Proof.MlKem.AArch64.Sample.kR s₀ := by rw [VG.Proof.MlKem.AArch64.stk, h]

theorem seed_frame {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) {m : Mem} (hf : Frame [VG.Proof.MlKem.AArch64.Sample.scR s₀, below s₀.sp 16] s₀.mem m) :
    bytesAt m (VG.Proof.MlKem.AArch64.Sample.sdP s₀) 34 = VG.Proof.MlKem.AArch64.Sample.Bs s₀ :=
  bytesAt_frame hf (fun r hr => by
    rcases VG.Proof.MlKem.AArch64.Sample.mem2 hr with rfl | rfl
    · exact hp.d_ss
    · rw [VG.Proof.MlKem.AArch64.Sample.below16]; exact hp.k_s.symm) (by decide)

/-- `absorb`, `pad` and `squeeze` of `len` bytes, then `R`. -/
theorem calls_ok (v : Proof.Sha3.AArch64.Permutation) {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) {s : State} (h : VG.Proof.MlKem.AArch64.Sample.AfterPro s₀ s) {len : Nat}
    (hl : len ≤ 840) (hlv : ((BitVec.ofNat 16 len).setWidth 64).toNat = len) {R : Prog isa}
    {Q : State → Prop} (hR : ∀ s', VG.Proof.MlKem.AArch64.Sample.Mid s₀ s' → VG.Proof.MlKem.AArch64.Sample.Buf len s₀ s'.mem → WP isa R s' Q) :
    WP isa (.seq (.call ("vg_keccak_absorb_scratch" ++ v.callee.suffix) (Impl.Sha3.AArch64.Stream.absorbWith v.callee)) <|
      .seq (.block samplePadArgs) <|
      .seq (.call ("vg_keccak_pad_scratch" ++ v.callee.suffix) (Impl.Sha3.AArch64.Stream.padWith v.callee)) <|
      .seq (.block (sampleSqueezeArgs len)) <|
      .seq (.call ("vg_keccak_squeeze_scratch" ++ v.callee.suffix) (Impl.Sha3.AArch64.Stream.squeezeWith v.callee)) R) s Q := by
  have hsd : ∀ {u : State}, VG.Proof.MlKem.AArch64.Sample.Mid s₀ u → 16 ≤ u.sp.toNat := fun hu => by rw [hu.sp]; exact hp.sp16
  have cw : ∀ {u : State}, VG.Proof.MlKem.AArch64.Sample.Mid s₀ u → ∀ {rs : List Region},
      (∀ r ∈ rs, ∃ off, r.base = VG.Proof.MlKem.AArch64.Sample.So s₀ off ∧ off + r.len ≤ 2048) → Covers rs u.wr :=
    fun hu _ h' => by rw [hu.wr]; exact VG.Proof.MlKem.AArch64.Sample.covers_sc hp h'
  have sub : ∀ {u : State}, VG.Proof.MlKem.AArch64.Sample.Mid s₀ u → ∀ {off n : Nat}, off + n ≤ 2048 →
      ∃ r' ∈ [VG.Proof.MlKem.AArch64.Sample.scR s₀, below s₀.sp 16], Region.Sub ⟨VG.Proof.MlKem.AArch64.Sample.So s₀ off, n⟩ r' :=
    fun _ _ _ h' => ⟨VG.Proof.MlKem.AArch64.Sample.scR s₀, List.mem_cons_self .., VG.Proof.MlKem.AArch64.Sample.sub_so s₀ h'⟩
  have subk : ∀ {u : State}, VG.Proof.MlKem.AArch64.Sample.Mid s₀ u → ∃ r' ∈ [VG.Proof.MlKem.AArch64.Sample.scR s₀, below s₀.sp 16], Region.Sub (below u.sp 16) r' :=
    fun hu => ⟨below s₀.sp 16, by simp, by rw [hu.sp]; exact fun _ h => h⟩
  -- absorb
  refine WP.seq (VG.Proof.MlKem.AArch64.absorb_callWith v (st := VG.Proof.MlKem.AArch64.Sample.So s₀ 840) (sc := VG.Proof.MlKem.AArch64.Sample.So s₀ 1040) h.x0 h.x1 h.x2 h.x3 h.x4 h.x5
    rate168 (by decide) (VG.Proof.MlKem.AArch64.Sample.disj_so s₀ (by omega) (by omega) (by omega))
    (hp.d_ss.sub_right (VG.Proof.MlKem.AArch64.Sample.sub_so s₀ (by omega))) (hp.d_ss.sub_right (VG.Proof.MlKem.AArch64.Sample.sub_so s₀ (by omega)))
    (hsd h.mid) (by rw [VG.Proof.MlKem.AArch64.Sample.stk_eq h.mid.sp]; exact VG.Proof.MlKem.AArch64.Sample.k_so hp (by omega)) (by rw [VG.Proof.MlKem.AArch64.Sample.stk_eq h.mid.sp]; exact hp.k_s)
    (by rw [VG.Proof.MlKem.AArch64.Sample.stk_eq h.mid.sp]; exact VG.Proof.MlKem.AArch64.Sample.k_so hp (by omega)) ?_ (cw h.mid ?_) fun s₁ k₁ r₁ _ => ?_)
  · rw [h.mid.rd, h.mid.wr, hp.rd, hp.wr]
    refine Covers.of_sub fun r hr => ?_
    rcases VG.Proof.MlKem.AArch64.Sample.mem3 hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.MlKem.AArch64.Sample.seedR s₀, by simp, 0, (ptr_zero _).symm, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨VG.Proof.MlKem.AArch64.Sample.scR s₀, by simp, 840, rfl, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨VG.Proof.MlKem.AArch64.Sample.scR s₀, by simp, 1040, rfl, Nat.le_of_ble_eq_true rfl⟩
  · intro r hr
    rcases VG.Proof.MlKem.AArch64.Sample.mem2 hr with rfl | rfl
    · exact ⟨840, rfl, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨1040, rfl, Nat.le_of_ble_eq_true rfl⟩
  have mid₁ : VG.Proof.MlKem.AArch64.Sample.Mid s₀ s₁ := h.mid.call k₁ (fun r hr => by
      rcases VG.Proof.MlKem.AArch64.Sample.mem3 hr with rfl | rfl | rfl
      · exact VG.Proof.MlKem.AArch64.Sample.sv_disj s₀ (by omega)
      · exact VG.Proof.MlKem.AArch64.Sample.sv_disj s₀ (by omega)
      · rw [h.mid.sp]; exact VG.Proof.MlKem.AArch64.Sample.sv_below hp)
    (fun r hr => by
      rcases VG.Proof.MlKem.AArch64.Sample.mem3 hr with rfl | rfl | rfl
      · exact sub h.mid (by omega)
      · exact sub h.mid (by omega)
      · exact subk h.mid)
  have rep₁ : Repr s₁.mem (VG.Proof.MlKem.AArch64.Sample.So s₀ 840) 168 (VG.Proof.MlKem.AArch64.Sample.Bs s₀) := by
    have := r₁ [] (repr_nil h.zero) (by decide)
    rwa [List.nil_append, VG.Proof.MlKem.AArch64.Sample.seed_frame hp h.mid.frame] at this
  -- pad
  refine WP.seq (wp_addImm (by decide) fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ => wp_movz fun s₄ h₄ e₄ =>
    wp_movz fun s₅ h₅ e₅ => wp_addImm (by decide) fun s₆ h₆ e₆ => wp_nil ?_)
  have k₆ := ((((h₂.keep.trans h₃.keep).trans h₄.keep).trans h₅.keep).trans h₆.keep)
  have m₆ : s₆.mem = s₁.mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem]
  have mid₆ := mid₁.keep k₆ m₆
  refine WP.seq (VG.Proof.MlKem.AArch64.pad_callWith v (st := VG.Proof.MlKem.AArch64.Sample.So s₀ 840) (sc := VG.Proof.MlKem.AArch64.Sample.So s₀ 1040) (rate := 168) (pos := 34)
    (by rw [h₆.get .x0, h₅.get .x0, h₄.get .x0, h₃.get .x0, e₂, mid₁.x26])
    (by rw [h₆.get .x1, h₅.get .x1, h₄.get .x1, e₃]; rfl) (by rw [h₆.get .x2, h₅.get .x2, e₄]; rfl)
    (by rw [e₆, h₅.get .x26, h₄.get .x26, h₃.get .x26, h₂.get .x26, mid₁.x26]) rate168 (by decide)
    (VG.Proof.MlKem.AArch64.Sample.disj_so s₀ (by omega) (by omega) (by omega)) (hsd mid₆)
    (by rw [VG.Proof.MlKem.AArch64.Sample.stk_eq mid₆.sp]; exact VG.Proof.MlKem.AArch64.Sample.k_so hp (by omega)) (by rw [VG.Proof.MlKem.AArch64.Sample.stk_eq mid₆.sp]; exact VG.Proof.MlKem.AArch64.Sample.k_so hp (by omega))
    (VG.Proof.MlKem.AArch64.Sample.covers_rw (cw mid₆ ?_)) (cw mid₆ ?_) fun s₇ k₇ r₇ => ?_)
  · intro r hr
    rcases VG.Proof.MlKem.AArch64.Sample.mem2 hr with rfl | rfl
    · exact ⟨840, rfl, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨1040, rfl, Nat.le_of_ble_eq_true rfl⟩
  · intro r hr
    rcases VG.Proof.MlKem.AArch64.Sample.mem2 hr with rfl | rfl
    · exact ⟨840, rfl, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨1040, rfl, Nat.le_of_ble_eq_true rfl⟩
  have mid₇ : VG.Proof.MlKem.AArch64.Sample.Mid s₀ s₇ := mid₆.call k₇ (fun r hr => by
      rcases VG.Proof.MlKem.AArch64.Sample.mem3 hr with rfl | rfl | rfl
      · exact VG.Proof.MlKem.AArch64.Sample.sv_disj s₀ (by omega)
      · exact VG.Proof.MlKem.AArch64.Sample.sv_disj s₀ (by omega)
      · rw [mid₆.sp]; exact VG.Proof.MlKem.AArch64.Sample.sv_below hp)
    (fun r hr => by
      rcases VG.Proof.MlKem.AArch64.Sample.mem3 hr with rfl | rfl | rfl
      · exact sub mid₆ (by omega)
      · exact sub mid₆ (by omega)
      · exact subk mid₆)
  have st₇ : stateAt s₇.mem (VG.Proof.MlKem.AArch64.Sample.So s₀ 840) = padded 168 shakeSuffix (VG.Proof.MlKem.AArch64.Sample.Bs s₀) := by
    have hs : (s₆.gpr .x3).setWidth 8 = shakeSuffix := by
      rw [h₆.get .x3, e₅]; decide
    have := r₇ (VG.Proof.MlKem.AArch64.Sample.Bs s₀) (by rw [m₆]; exact rep₁) (by rw [bytesAt_length])
    rw [hs] at this
    exact this
  -- squeeze
  refine WP.seq (wp_addImm (by decide) fun s₈ h₈ e₈ => wp_movz fun s₉ h₉ e₉ => wp_movz fun s₁₀ h₁₀ e₁₀ =>
    wp_mov fun s₁₁ h₁₁ e₁₁ => wp_movz fun s₁₂ h₁₂ e₁₂ => wp_addImm (by decide) fun s₁₃ h₁₃ e₁₃ =>
    wp_nil ?_)
  have k₁₃ := (((((h₈.keep.trans h₉.keep).trans h₁₀.keep).trans h₁₁.keep).trans h₁₂.keep).trans h₁₃.keep)
  have m₁₃ : s₁₃.mem = s₇.mem := by rw [h₁₃.mem, h₁₂.mem, h₁₁.mem, h₁₀.mem, h₉.mem, h₈.mem]
  have mid₁₃ := mid₇.keep k₁₃ m₁₃
  refine WP.seq (VG.Proof.MlKem.AArch64.squeeze_callWith v (st := VG.Proof.MlKem.AArch64.Sample.So s₀ 840) (out := VG.Proof.MlKem.AArch64.Sample.So s₀ 0) (sc := VG.Proof.MlKem.AArch64.Sample.So s₀ 1040) (rate := 168)
    (pos := 0) (len := len)
    (by rw [h₁₃.get .x0, h₁₂.get .x0, h₁₁.get .x0, h₁₀.get .x0, h₉.get .x0, e₈, mid₇.x26])
    (by rw [h₁₃.get .x1, h₁₂.get .x1, h₁₁.get .x1, h₁₀.get .x1, e₉]; rfl)
    (by rw [h₁₃.get .x2, h₁₂.get .x2, h₁₁.get .x2, e₁₀]; rfl)
    (by rw [h₁₃.get .x3, h₁₂.get .x3, e₁₁, h₁₀.get .x26, h₉.get .x26, h₈.get .x26, mid₇.x26]; exact (ptr_zero _).symm)
    (by rw [h₁₃.get .x4, e₁₂]; exact hlv)
    (by rw [e₁₃, h₁₂.get .x26, h₁₁.get .x26, h₁₀.get .x26, h₉.get .x26, h₈.get .x26, mid₇.x26])
    rate168 (by decide) (VG.Proof.MlKem.AArch64.Sample.disj_so s₀ (by omega) (by omega) (by omega))
    (VG.Proof.MlKem.AArch64.Sample.disj_so s₀ (by omega) (by omega) (by omega)) (VG.Proof.MlKem.AArch64.Sample.disj_so s₀ (by omega) (by omega) (by omega))
    (hsd mid₁₃) (by rw [VG.Proof.MlKem.AArch64.Sample.stk_eq mid₁₃.sp]; exact VG.Proof.MlKem.AArch64.Sample.k_so hp (by omega))
    (by rw [VG.Proof.MlKem.AArch64.Sample.stk_eq mid₁₃.sp]; exact VG.Proof.MlKem.AArch64.Sample.k_so hp (by omega)) (by rw [VG.Proof.MlKem.AArch64.Sample.stk_eq mid₁₃.sp]; exact VG.Proof.MlKem.AArch64.Sample.k_so hp (by omega))
    (VG.Proof.MlKem.AArch64.Sample.covers_rw (cw mid₁₃ ?_)) (cw mid₁₃ ?_) fun s₁₄ k₁₄ r₁₄ _ _ => ?_)
  · intro r hr
    rcases VG.Proof.MlKem.AArch64.Sample.mem3 hr with rfl | rfl | rfl
    · exact ⟨840, rfl, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨0, rfl, by show 0 + len ≤ 2048; omega⟩
    · exact ⟨1040, rfl, Nat.le_of_ble_eq_true rfl⟩
  · intro r hr
    rcases VG.Proof.MlKem.AArch64.Sample.mem3 hr with rfl | rfl | rfl
    · exact ⟨840, rfl, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨0, rfl, by show 0 + len ≤ 2048; omega⟩
    · exact ⟨1040, rfl, Nat.le_of_ble_eq_true rfl⟩
  have mid₁₄ : VG.Proof.MlKem.AArch64.Sample.Mid s₀ s₁₄ := mid₁₃.call k₁₄ (fun r hr => by
      rcases VG.Proof.MlKem.AArch64.Sample.mem4 hr with rfl | rfl | rfl | rfl
      · exact VG.Proof.MlKem.AArch64.Sample.sv_disj s₀ (by omega)
      · exact VG.Proof.MlKem.AArch64.Sample.sv_disj s₀ (by omega)
      · exact VG.Proof.MlKem.AArch64.Sample.sv_disj s₀ (by omega)
      · rw [mid₁₃.sp]; exact VG.Proof.MlKem.AArch64.Sample.sv_below hp)
    (fun r hr => by
      rcases VG.Proof.MlKem.AArch64.Sample.mem4 hr with rfl | rfl | rfl | rfl
      · exact sub mid₁₃ (by omega)
      · exact sub mid₁₃ (by omega)
      · exact sub mid₁₃ (by omega)
      · exact subk mid₁₃)
  refine hR s₁₄ mid₁₄ fun p hp' => ?_
  rw [m₁₃, st₇, ← xof_eq] at r₁₄
  rw [← bytesAt_getD s₁₄.mem (VG.Proof.MlKem.AArch64.Sample.So s₀ 0) hp', r₁₄, xof_getD _ hp']

/-! ## `a` set to zeros, and the registers back -/

/-- After `k` coefficients of `a` set to zero. -/
structure ZInv (s₀ s₁ : State) (k : Nat) (u : State) : Prop where
  keep : Keep [.x3, .x4] s₁ u
  x3 : u.gpr .x3 = coeffAddr (VG.Proof.MlKem.AArch64.Sample.aP s₀) k
  x4 : (u.gpr .x4).toNat = 256 - k
  coeffs : CoeffsUpTo u.mem (VG.Proof.MlKem.AArch64.Sample.aP s₀) k (fun _ => 0) fun i => coeffAt s₁.mem (VG.Proof.MlKem.AArch64.Sample.aP s₀) i
  frame : Frame [VG.Proof.MlKem.AArch64.Sample.aR s₀] s₁.mem u.mem

theorem zero_step {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) {s₁ : State} (hw : s₁.wr = s₀.wr) (h9 : s₁.gpr .x9 = 0)
    {k : Nat} (hk : k < 256) {u : State} (h : VG.Proof.MlKem.AArch64.Sample.ZInv s₀ s₁ k u) :
    WP isa (.block zeroBody) u fun u' => VG.Proof.MlKem.AArch64.Sample.ZInv s₀ s₁ (k + 1) u' ∧ ((u'.gpr .x4).toNat ≠ 0 ↔ k + 1 ≠ 256) := by
  have hin : InRegions u.wr (coeffAddr (VG.Proof.MlKem.AArch64.Sample.aP s₀) k) 4 := by
    rw [h.keep.wr, hw, hp.wr]
    exact in_regions (List.mem_cons_self ..) (coeff_contains _ (show k < n from hk))
  refine wp_strw (a := coeffAddr (VG.Proof.MlKem.AArch64.Sample.aP s₀) k) (by decide) (by rw [h.x3, ptr_zero]) hin fun u₁ h₁ =>
    wp_addImm (by decide) fun u₂ h₂ e₂ => wp_subImm (by decide) fun u₃ h₃ e₃ => wp_nil ?_
  have c4 : (u₂.gpr .x4).toNat = 256 - k := by rw [h₂.get .x4, h₁.gpr, h.x4]
  have v4 : (u₃.gpr .x4).toNat = 256 - (k + 1) := by
    rw [e₃, toNat_sub_n (by rw [c4]; simp; omega), c4]
    simp
    omega
  have m₃ : u₃.mem = u.mem.writeW (coeffAddr (VG.Proof.MlKem.AArch64.Sample.aP s₀) k) ((u.gpr .x9).setWidth 32) := by
    rw [h₃.mem, h₂.mem, h₁.mem]
  have z : (u.gpr .x9).setWidth 32 = 0 := by rw [h.keep.get .x9, h9]; rfl
  refine ⟨⟨(h.keep.trans ((h₁.keep.trans h₂.keep).trans h₃.keep)).mono, ?_, v4, ?_, ?_⟩,
    by rw [v4]; omega⟩
  · rw [h₃.get .x3, e₂, h₁.gpr, h.x3, coeffAddr, coeffAddr, ptr_next]
  · rw [m₃, z]; exact CoeffsUpTo.write h.coeffs hk rfl
  · rw [m₃]
    exact h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ (show k < n from hk))

/-- The registers and permissions on exit, as on entry. -/
structure Fin (s₀ u : State) : Prop where
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr
  sp : u.sp = s₀.sp
  cs : ∀ r ∈ preserved, u.gpr r = s₀.gpr r
  vcs : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64

/-- After the setup of the loop, our caller's registers still saved: `Mid`,
but for the memory, of which the seed is kept. -/
structure MidA (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x24 : s.gpr .x24 = VG.Proof.MlKem.AArch64.Sample.sdP s₀
  x25 : s.gpr .x25 = VG.Proof.MlKem.AArch64.Sample.aP s₀
  x26 : s.gpr .x26 = VG.Proof.MlKem.AArch64.Sample.scP s₀
  cs : ∀ r ∈ preserved, r ≠ .x24 → r ≠ .x25 → r ≠ .x26 → r ≠ .x30 → s.gpr r = s₀.gpr r
  sv : VG.Proof.MlKem.AArch64.Sample.Saved s₀ s.mem
  seed : bytesAt s.mem (VG.Proof.MlKem.AArch64.Sample.sdP s₀) 34 = VG.Proof.MlKem.AArch64.Sample.Bs s₀
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64

theorem sv_a {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) : ∀ r ∈ [VG.Proof.MlKem.AArch64.Sample.aR s₀], Region.Disjoint ⟨VG.Proof.MlKem.AArch64.Sample.So s₀ 1680, 32⟩ r :=
  fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (hp.d_as.sub_right (VG.Proof.MlKem.AArch64.Sample.sub_so s₀ (by omega))).symm

/-- `MidA` after code that writes only `a` and registers other than the
callee-saved ones. -/
theorem MidA.keep {s₀ s s' : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) (h : VG.Proof.MlKem.AArch64.Sample.MidA s₀ s) {regs : List Reg}
    (hk : Keep regs s s') (hf : Frame [VG.Proof.MlKem.AArch64.Sample.aR s₀] s.mem s'.mem)
    (hr : ∀ r ∈ regs, r ∉ preserved := by decide) : VG.Proof.MlKem.AArch64.Sample.MidA s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp],
    by rw [hk.get .x24 (fun h' => hr _ h' (by decide)), h.x24],
    by rw [hk.get .x25 (fun h' => hr _ h' (by decide)), h.x25],
    by rw [hk.get .x26 (fun h' => hr _ h' (by decide)), h.x26],
    fun r hp' h24 h25 h26 h30 => by
      rw [hk.get r (fun h' => hr _ h' hp'), h.cs r hp' h24 h25 h26 h30],
    h.sv.frame hf (VG.Proof.MlKem.AArch64.Sample.sv_a hp),
    by rw [← h.seed]; exact bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hp.d_sa) (by decide), fun r hr => (hk.vcs r hr).trans (h.vcs r hr)⟩

theorem pres_x34 : ∀ r ∈ preserved, r ∉ [Reg.x3, .x4] := by decide

/-- `a` set to zeros, and the loop's registers for `N` iterations. -/
theorem restN_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) {len N : Nat} (hN : 3 * N ≤ len) (hl : len ≤ 840)
    (hv : ((BitVec.ofNat 16 N).setWidth 64).toNat = N) {s : State} (h : VG.Proof.MlKem.AArch64.Sample.Mid s₀ s)
    (hb : VG.Proof.MlKem.AArch64.Sample.Buf len s₀ s.mem) :
    WP isa sampleZero s fun u => WP isa (.block (sampleRegs N)) u fun v =>
      VG.Proof.MlKem.AArch64.Sample.LPre N (VG.Proof.MlKem.AArch64.Sample.Bs s₀) (VG.Proof.MlKem.AArch64.Sample.So s₀ 0) (VG.Proof.MlKem.AArch64.Sample.aP s₀) v ∧ VG.Proof.MlKem.AArch64.Sample.MidA s₀ v := by
  refine WP.seq (wp_movz fun s₁ h₁ e₁ => wp_mov fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ => wp_nil ?_)
  have k₃ := (h₁.keep.trans h₂.keep).trans h₃.keep
  have m₃ : s₃.mem = s.mem := by rw [h₃.mem, h₂.mem, h₁.mem]
  have mid₃ := h.keep k₃ m₃
  have z9 : s₃.gpr .x9 = 0 := by rw [h₃.get .x9, h₂.get .x9, e₁]; rfl
  have i₀ : VG.Proof.MlKem.AArch64.Sample.ZInv s₀ s₃ 0 s₃ := ⟨Keep.refl _ _,
    by rw [h₃.get .x3, e₂, h₁.get .x25, h.x25, coeffAddr, Nat.mul_zero, ptr_zero],
    by rw [e₃]; rfl, CoeffsUpTo.zero _, Frame.refl _ _⟩
  refine WP.mono (count_loop (by decide) (VG.Proof.MlKem.AArch64.Sample.ZInv s₀ s₃) (fun k hk u hu => VG.Proof.MlKem.AArch64.Sample.zero_step hp mid₃.wr z9 hk hu) i₀)
    fun s₄ h₄ => ?_
  have midA₄ : VG.Proof.MlKem.AArch64.Sample.MidA s₀ s₄ := MidA.keep hp
    ⟨mid₃.rd, mid₃.wr, mid₃.sp, mid₃.x24, mid₃.x25, mid₃.x26, mid₃.cs, mid₃.sv,
      VG.Proof.MlKem.AArch64.Sample.seed_frame hp mid₃.frame, mid₃.vcs⟩ h₄.keep h₄.frame
  refine wp_mov fun s₅ h₅ e₅ => wp_mov fun s₆ h₆ e₆ => wp_movz fun s₇ h₇ e₇ => wp_movz fun s₈ h₈ e₈ =>
    wp_movz fun s₉ h₉ e₉ => wp_movz fun s₁₀ h₁₀ e₁₀ => wp_nil ?_
  have k₁₀ := ((((h₅.keep.trans h₆.keep).trans h₇.keep).trans h₈.keep).trans h₉.keep).trans h₁₀.keep
  have m₁₀ : s₁₀.mem = s₄.mem := by rw [h₁₀.mem, h₉.mem, h₈.mem, h₇.mem, h₆.mem, h₅.mem]
  have wr₄ : s₄.wr = s₀.wr := midA₄.wr
  have rd₄ : s₄.rd = s₀.rd := midA₄.rd
  have hl' := h₄.coeffs
  refine ⟨⟨fun p hp' => ?_, fun p hp' => ?_, fun i hi => ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩, MidA.keep hp midA₄ k₁₀ (by rw [m₁₀]; exact Frame.refl _ _)⟩
  · rw [m₁₀, byte_frame h₄.frame (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hp.d_as.sub_right (VG.Proof.MlKem.AArch64.Sample.sub_so s₀ (by omega))).symm)
      (by decide) (show p < 840 by omega), m₃, hb p (by omega)]
  · rw [k₁₀.rd, k₁₀.wr, rd₄, wr₄, VG.Proof.MlKem.AArch64.Sample.So, ptr_add, Nat.zero_add]
    exact in_rd_wr (VG.Proof.MlKem.AArch64.Sample.in_sc hp (by omega))
  · rw [k₁₀.wr, wr₄, hp.wr]
    exact in_regions (List.mem_cons_self ..) (coeff_contains _ (show i < n from hi))
  · exact (hp.d_as.sub_right (VG.Proof.MlKem.AArch64.Sample.sub_so s₀ (by omega))).symm
  · rw [m₁₀, hl' i hi, ite_eq_left hi]
  · rw [h₁₀.get .x2, h₉.get .x2, h₈.get .x2, h₇.get .x2, h₆.get .x2, e₅, midA₄.x26]
    exact (ptr_zero _).symm
  · rw [h₁₀.get .x3, h₉.get .x3, h₈.get .x3, h₇.get .x3, e₆, h₅.get .x25, midA₄.x25]
  · rw [h₁₀.get .x4, h₉.get .x4, h₈.get .x4, e₇]; rfl
  · rw [h₁₀.get .x5, h₉.get .x5, e₈]; exact hv
  · rw [h₁₀.get .x9, e₉]; rfl
  · rw [e₁₀]; rfl
  · omega

/-- The registers `sampleRestore` loads. -/
abbrev restoreRegs : List Reg := [.x30, .x24, .x25, .x26]

theorem LPre.keep {N : Nat} {B : List Byte} {bP aP : Addr} {s s' : State} (h : VG.Proof.MlKem.AArch64.Sample.LPre N B bP aP s)
    (hk : Keep VG.Proof.MlKem.AArch64.Sample.restoreRegs s s') (hm : s'.mem = s.mem) : VG.Proof.MlKem.AArch64.Sample.LPre N B bP aP s' :=
  ⟨fun p hp' => by rw [hm]; exact h.buf p hp', fun p hp' => by rw [hk.rd, hk.wr]; exact h.inb p hp',
    fun i hi => by rw [hk.wr]; exact h.ina i hi, h.disj, fun i hi => by rw [hm]; exact h.zero i hi,
    by rw [hk.get .x2, h.x2], by rw [hk.get .x3, h.x3], by rw [hk.get .x4, h.x4],
    by rw [hk.get .x5, h.x5], by rw [hk.get .x9, h.x9], by rw [hk.get .x10, h.x10], h.bound⟩

/-- Our caller's registers back from `scratch`. -/
theorem restore_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) {s : State} (h : VG.Proof.MlKem.AArch64.Sample.MidA s₀ s) {P : State → Prop}
    (hP : ∀ u, Keep VG.Proof.MlKem.AArch64.Sample.restoreRegs s u → u.mem = s.mem → P u) :
    WP isa (.block sampleRestore) s fun u => P u ∧ VG.Proof.MlKem.AArch64.Sample.Fin s₀ u := by
  have in₄ : ∀ {off : Nat}, off + 8 ≤ 2048 → InRegions (s.rd ++ s.wr) (VG.Proof.MlKem.AArch64.Sample.So s₀ off) 8 :=
    fun h' => by rw [h.wr]; exact in_rd_wr (VG.Proof.MlKem.AArch64.Sample.in_sc hp h')
  refine wp_ldrx (a := VG.Proof.MlKem.AArch64.Sample.So s₀ 1696) (by decide) (by rw [h.x26]) (in₄ (by omega)) fun s₁ h₁ e₁ => ?_
  refine wp_ldrx (a := VG.Proof.MlKem.AArch64.Sample.So s₀ 1704) (by decide) (by rw [h₁.get .x26, h.x26])
    (by rw [h₁.rd, h₁.wr]; exact in₄ (by omega)) fun s₂ h₂ e₂ => ?_
  refine wp_ldrx (a := VG.Proof.MlKem.AArch64.Sample.So s₀ 1680) (by decide) (by rw [h₂.get .x26, h₁.get .x26, h.x26])
    (by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact in₄ (by omega)) fun s₃ h₃ e₃ => ?_
  refine wp_ldrx (a := VG.Proof.MlKem.AArch64.Sample.So s₀ 1688) (by decide) (by rw [h₃.get .x26, h₂.get .x26, h₁.get .x26, h.x26])
    (by rw [h₃.rd, h₃.wr, h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact in₄ (by omega)) fun s₄ h₄ e₄ => wp_nil ?_
  have k₄ := ((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep
  have m₄ : s₄.mem = s.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨hP s₄ (k₄.mono (by decide)) m₄, by rw [k₄.rd, h.rd], by rw [k₄.wr, h.wr],
    by rw [k₄.sp, h.sp], (fun r hr => ?_), fun r hr => (k₄.vcs r hr).trans (h.vcs r hr)⟩
  have sv := h.sv
  by_cases h30 : r = .x30
  · subst h30; rw [h₄.get .x30, h₃.get .x30, h₂.get .x30, e₁]; exact sv.2.2.1
  by_cases h24 : r = .x24
  · subst h24; rw [h₄.get .x24, h₃.get .x24, e₂, h₁.mem]; exact sv.2.2.2
  by_cases h25 : r = .x25
  · subst h25; rw [h₄.get .x25, e₃, h₂.mem, h₁.mem]; exact sv.1
  by_cases h26 : r = .x26
  · subst h26; rw [e₄, h₃.mem, h₂.mem, h₁.mem]; exact sv.2.1
  rw [k₄.gpr r (by simp [h30, h24, h25, h26]), h.cs r hr h24 h25 h26 h30]

theorem rest_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) {s : State} (h : VG.Proof.MlKem.AArch64.Sample.Mid s₀ s) (hb : VG.Proof.MlKem.AArch64.Sample.Buf 840 s₀ s.mem) :
    WP isa (.seq sampleZero (.block sampleSetup)) s fun u =>
      VG.Proof.MlKem.AArch64.Sample.LPre 280 (VG.Proof.MlKem.AArch64.Sample.Bs s₀) (VG.Proof.MlKem.AArch64.Sample.So s₀ 0) (VG.Proof.MlKem.AArch64.Sample.aP s₀) u ∧ VG.Proof.MlKem.AArch64.Sample.Fin s₀ u := by
  refine WP.seq (WP.mono (VG.Proof.MlKem.AArch64.Sample.restN_ok hp (N := 280) (by decide) (Nat.le_refl _) (by decide) h hb)
    fun u hu => ?_)
  rw [sampleSetup, WP.block_append_iff]
  exact WP.mono hu fun v ⟨hl, hm⟩ => VG.Proof.MlKem.AArch64.Sample.restore_ok hp hm fun u hk hm' => hl.keep hk hm'

end VG.Proof.MlKem.AArch64.Sample

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.Sample`. -/
section

/-!
# ML-KEM on AArch64: `vg_mlkem_sample_ntt`

`sampleFull`, from any state satisfying the precondition, is `phaseA_ok` (the
SHAKE128 output, `a` zero) followed by `loop_ok` (`full_ok`). `sampleFast` is
the same with 504 bytes and 168 iterations (`fast_ok`); if they leave 256
coefficients, they are `SampleNTT`'s (`sampleNTT_of_full`), and otherwise
`sampleFull` runs from the original arguments, which `sampleRetry` restores
(`retry_ok`).

Constant time up to the seed, relating two runs (`RelCT`) from states that
agree on the pointers and on the seed: up to each loop, the taint analysis
(through the Keccak calls); then, by correctness, both runs have the same
SHAKE128 output (a function of the seed) in `scratch` and zeros in `a`, so
the loop, which touches nothing else, runs with permissions on only memory
both runs agree on (`RelCT.narrow`), where `memTaint` proves it leaks the
same (its branches depend on the output). By correctness again, both runs
of `sampleFast` leave the same number of coefficients, on which the retry
branches, and the retry is `sampleFull` from states that satisfy its
contract (`full_ct`).
-/

namespace VG.Proof.MlKem.AArch64.Sample

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem phaseA_ok (v : Proof.Sha3.AArch64.Permutation) {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) :
    WP isa (sampleSqueezeWith v.callee) s₀ fun u => VG.Proof.MlKem.AArch64.Sample.LPre 280 (VG.Proof.MlKem.AArch64.Sample.Bs s₀) (VG.Proof.MlKem.AArch64.Sample.So s₀ 0) (VG.Proof.MlKem.AArch64.Sample.aP s₀) u ∧ VG.Proof.MlKem.AArch64.Sample.Fin s₀ u :=
  WP.seq (WP.mono (VG.Proof.MlKem.AArch64.Sample.prologue_ok hp) fun _ h => VG.Proof.MlKem.AArch64.Sample.calls_ok v hp h (by decide) (by decide) fun _ m b =>
    VG.Proof.MlKem.AArch64.Sample.rest_ok hp m b)

theorem pres_loop : ∀ r ∈ preserved, r ∉ (Reg.x0 :: VG.Proof.MlKem.AArch64.Sample.lRegs) := by decide

/-- What the code guarantees: `sampleStrong`'s postcondition, and the ABI. -/
def Post (s₀ s' : State) : Prop :=
  abiPreserved s₀ s' ∧ Reduced s'.mem (VG.Proof.MlKem.AArch64.Sample.aP s₀) ∧
    ((s'.gpr .x0 = 1 ∧ sampleNTT 280 (VG.Proof.MlKem.AArch64.Sample.Bs s₀) = some (polyAt s'.mem (VG.Proof.MlKem.AArch64.Sample.aP s₀))) ∨
      (s'.gpr .x0 = 0 ∧ sampleNTT 280 (VG.Proof.MlKem.AArch64.Sample.Bs s₀) = none))

theorem full_ok (v : Proof.Sha3.AArch64.Permutation) {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) : WP isa (sampleFullWith v.callee) s₀ (VG.Proof.MlKem.AArch64.Sample.Post s₀) := by
  refine WP.seq (WP.mono ((VG.Proof.MlKem.AArch64.Sample.phaseA_ok v) hp) fun u ⟨hl, hf⟩ => WP.mono (VG.Proof.MlKem.AArch64.Sample.loop_ok hl) fun s' ⟨k, _, res⟩ => ?_)
  refine ⟨⟨fun r hr => ?_, ?_, fun r hr => (k.vcs r hr).trans (hf.vcs r hr)⟩, res.1, ?_⟩
  · rw [k.gpr r (VG.Proof.MlKem.AArch64.Sample.pres_loop r hr), hf.cs r hr]
  · rw [k.sp, hf.sp]
  rcases res.2 with ⟨h0, hpoly, hs⟩ | ⟨h0, hn⟩
  · exact .inl ⟨h0, by rw [hpoly.2]; exact hs⟩
  · exact .inr ⟨h0, hn⟩

/-! ## `sampleFast` -/

theorem fastA_ok (v : Proof.Sha3.AArch64.Permutation) {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) :
    WP isa ((sampleSqueezeNWith v.callee) 504 (sampleRegs 168)) s₀ fun u =>
      VG.Proof.MlKem.AArch64.Sample.LPre 168 (VG.Proof.MlKem.AArch64.Sample.Bs s₀) (VG.Proof.MlKem.AArch64.Sample.So s₀ 0) (VG.Proof.MlKem.AArch64.Sample.aP s₀) u ∧ VG.Proof.MlKem.AArch64.Sample.MidA s₀ u :=
  WP.seq (WP.mono (VG.Proof.MlKem.AArch64.Sample.prologue_ok hp) fun _ h => VG.Proof.MlKem.AArch64.Sample.calls_ok v hp h (by decide) (by decide) fun _ m b =>
    WP.seq (VG.Proof.MlKem.AArch64.Sample.restN_ok hp (by decide) (by decide) (by decide) m b))

/-- What `sampleFast` leaves: our caller's registers still saved, and the
coefficients of 168 iterations in `a`. -/
structure FastPost (s₀ u : State) : Prop where
  mid : VG.Proof.MlKem.AArch64.Sample.MidA s₀ u
  len : (VG.Proof.MlKem.AArch64.Sample.LA (VG.Proof.MlKem.AArch64.Sample.Bs s₀) 168).length ≤ 256
  x4 : (u.gpr .x4).toNat = 256 - (VG.Proof.MlKem.AArch64.Sample.LA (VG.Proof.MlKem.AArch64.Sample.Bs s₀) 168).length
  coeffs : VG.Proof.MlKem.AArch64.Sample.Coeffs u.mem (VG.Proof.MlKem.AArch64.Sample.aP s₀) (VG.Proof.MlKem.AArch64.Sample.LA (VG.Proof.MlKem.AArch64.Sample.Bs s₀) 168)

theorem fastLoop_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) {u : State} (hl : VG.Proof.MlKem.AArch64.Sample.LPre 168 (VG.Proof.MlKem.AArch64.Sample.Bs s₀) (VG.Proof.MlKem.AArch64.Sample.So s₀ 0) (VG.Proof.MlKem.AArch64.Sample.aP s₀) u)
    (hm : VG.Proof.MlKem.AArch64.Sample.MidA s₀ u) : WP isa (.loop sampleBody (.nonzero .x .x5)) u (VG.Proof.MlKem.AArch64.Sample.FastPost s₀) :=
  WP.mono (VG.Proof.MlKem.AArch64.Sample.iters_ok (by decide) hl) fun _ hv =>
    ⟨MidA.keep hp hm hv.keep hv.acc.frame, hv.acc.len, hv.acc.x4, hv.acc.coeffs⟩

theorem fast_ok (v : Proof.Sha3.AArch64.Permutation) {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) : WP isa (sampleFastWith v.callee) s₀ (VG.Proof.MlKem.AArch64.Sample.FastPost s₀) :=
  WP.seq (WP.mono ((VG.Proof.MlKem.AArch64.Sample.fastA_ok v) hp) fun _ ⟨hl, hm⟩ => VG.Proof.MlKem.AArch64.Sample.fastLoop_ok hp hl hm)

/-- 256 coefficients after 168 iterations: 1, and `SampleNTT`. -/
theorem done_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) {u : State} (h : VG.Proof.MlKem.AArch64.Sample.FastPost s₀ u)
    (hz : (u.gpr .x4).toNat = 0) : WP isa (.block sampleDone) u (VG.Proof.MlKem.AArch64.Sample.Post s₀) := by
  have hf : (VG.Proof.MlKem.AArch64.Sample.LA (VG.Proof.MlKem.AArch64.Sample.Bs s₀) 168).length = 256 := by have := h.x4; have := h.len; omega
  refine wp_movz fun u₁ h₁ e₁ => ?_
  have m₁ : VG.Proof.MlKem.AArch64.Sample.MidA s₀ u₁ := MidA.keep hp h.mid h₁.keep (by rw [h₁.mem]; exact Frame.refl _ _)
  refine WP.mono (VG.Proof.MlKem.AArch64.Sample.restore_ok hp m₁ (P := fun v => v.gpr .x0 = 1 ∧ v.mem = u.mem)
    fun v hk hm => ⟨by rw [hk.get .x0, e₁]; rfl, by rw [hm, h₁.mem]⟩) fun s' ⟨⟨h0, hm⟩, hfin⟩ => ?_
  have hc := h.coeffs.full hf
  rw [hf] at hc
  refine ⟨⟨hfin.cs, hfin.sp, hfin.vcs⟩, ?_, .inl ⟨h0, ?_⟩⟩
  · rw [hm]; exact VG.Proof.MlKem.AArch64.Sample.reduced_of_coeffs (L := VG.Proof.MlKem.AArch64.Sample.LA (VG.Proof.MlKem.AArch64.Sample.Bs s₀) 168) (by rw [hf]; exact hc)
  · rw [sampleNTT_of_full (by decide : 168 ≤ 280) hf]
    refine congrArg some ?_
    exact ((CoeffsUpTo.polyIs (by rw [hm]; exact hc) fun i hi => VG.Proof.MlKem.AArch64.Sample.cv_toPoly hi).2).symm

/-- The original arguments, restored for `sampleFull`. -/
structure RetryPost (s₀ v : State) : Prop where
  rd : v.rd = s₀.rd
  wr : v.wr = s₀.wr
  sp : v.sp = s₀.sp
  x0 : v.gpr .x0 = VG.Proof.MlKem.AArch64.Sample.sdP s₀
  x1 : v.gpr .x1 = VG.Proof.MlKem.AArch64.Sample.aP s₀
  x2 : v.gpr .x2 = VG.Proof.MlKem.AArch64.Sample.scP s₀
  cs : ∀ r ∈ preserved, v.gpr r = s₀.gpr r
  seed : bytesAt v.mem (VG.Proof.MlKem.AArch64.Sample.sdP s₀) 34 = VG.Proof.MlKem.AArch64.Sample.Bs s₀
  vcs : ∀ r ∈ preservedV, (v.v r).extractLsb' 0 64 = (s₀.v r).extractLsb' 0 64

theorem retryBlock_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) {u : State} (h : VG.Proof.MlKem.AArch64.Sample.FastPost s₀ u) :
    WP isa (.block sampleRetry) u (VG.Proof.MlKem.AArch64.Sample.RetryPost s₀) := by
  rw [sampleRetry, WP.block_append_iff]
  refine wp_mov fun u₁ h₁ e₁ => wp_mov fun u₂ h₂ e₂ => wp_mov fun u₃ h₃ e₃ => wp_nil ?_
  have k₃ := (h₁.keep.trans h₂.keep).trans h₃.keep
  have m₃ : VG.Proof.MlKem.AArch64.Sample.MidA s₀ u₃ := MidA.keep hp h.mid k₃ (by rw [h₃.mem, h₂.mem, h₁.mem]; exact Frame.refl _ _)
  refine WP.mono (VG.Proof.MlKem.AArch64.Sample.restore_ok hp m₃ (P := fun v => v.gpr .x0 = VG.Proof.MlKem.AArch64.Sample.sdP s₀ ∧ v.gpr .x1 = VG.Proof.MlKem.AArch64.Sample.aP s₀ ∧
    v.gpr .x2 = VG.Proof.MlKem.AArch64.Sample.scP s₀ ∧ v.mem = u₃.mem) fun v hk hm => ⟨?_, ?_, ?_, hm⟩)
    fun v ⟨⟨e0, e1, e2, hm⟩, hfin⟩ => ⟨hfin.rd, hfin.wr, hfin.sp, e0, e1, e2, hfin.cs, by rw [hm]; exact m₃.seed, hfin.vcs⟩
  · rw [hk.get .x0, h₃.get .x0, h₂.get .x0, e₁, h.mid.x24]
  · rw [hk.get .x1, h₃.get .x1, e₂, h₁.get .x25, h.mid.x25]
  · rw [hk.get .x2, e₃, h₂.get .x26, h₁.get .x26, h.mid.x26]

theorem RetryPost.pre {s₀ v : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) (h : VG.Proof.MlKem.AArch64.Sample.RetryPost s₀ v) : sampleAArch64.pre v := by
  simp only [VG.Proof.MlKem.sampleAArch64, h.x0, h.x1, h.x2, h.rd, h.wr, h.sp]
  exact ⟨hp.rd, hp.wr, hp.d_sa, hp.d_ss, hp.d_as, hp.sp16, hp.k_s, hp.k_a, hp.k_c⟩

/-- Fewer: the original arguments back, and `sampleFull` from them. -/
theorem retry_ok (v : Proof.Sha3.AArch64.Permutation) {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) {u : State} (h : VG.Proof.MlKem.AArch64.Sample.FastPost s₀ u) :
    WP isa (.seq (.block sampleRetry) (sampleFullWith v.callee)) u (VG.Proof.MlKem.AArch64.Sample.Post s₀) := by
  refine WP.seq (WP.mono (VG.Proof.MlKem.AArch64.Sample.retryBlock_ok hp h) fun u₁ hv => ?_)
  refine WP.mono ((VG.Proof.MlKem.AArch64.Sample.full_ok v) (VG.Proof.MlKem.AArch64.Sample.pre_of (hv.pre hp))) fun s' ⟨⟨cs, sp, vcs⟩, red, res⟩ => ?_
  have hB : VG.Proof.MlKem.AArch64.Sample.Bs u₁ = VG.Proof.MlKem.AArch64.Sample.Bs s₀ := by simp only [VG.Proof.MlKem.AArch64.Sample.Bs, VG.Proof.MlKem.AArch64.Sample.sdP, hv.x0]; exact hv.seed
  refine ⟨⟨fun r hr => by rw [cs r hr, hv.cs r hr], by rw [sp, hv.sp], fun r hr => (vcs r hr).trans (hv.vcs r hr)⟩, ?_, ?_⟩
  · simpa only [VG.Proof.MlKem.AArch64.Sample.aP, hv.x1] using red
  · simpa only [VG.Proof.MlKem.AArch64.Sample.aP, hv.x1, hB] using res

theorem strong_ok (v : Proof.Sha3.AArch64.Permutation) {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) : WP isa (sampleNTTWith v.callee) s₀ (VG.Proof.MlKem.AArch64.Sample.Post s₀) := by
  refine WP.seq (WP.mono ((VG.Proof.MlKem.AArch64.Sample.fast_ok v) hp) fun u h => ?_)
  refine WP.ite (u.gpr .x4 == 0) (VG.Proof.MlKem.AArch64.eval_zero _ _) (fun hz => ?_) (fun _ => (VG.Proof.MlKem.AArch64.Sample.retry_ok v) hp h)
  rw [eq_zero_iff, decide_eq_true_eq] at hz
  exact VG.Proof.MlKem.AArch64.Sample.done_ok hp h hz

theorem correct (v : Proof.Sha3.AArch64.Permutation) {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre s₀) :
    WP isa (sampleNTTWith v.callee) s₀ fun s' => abiPreserved s₀ s' ∧ sampleAArch64.post s₀ s' := by
  refine WP.mono ((VG.Proof.MlKem.AArch64.Sample.strong_ok v) hp) fun s' ⟨abi, red, res⟩ => ⟨abi, ?_⟩
  rcases res with ⟨h0, hs⟩ | ⟨h0, hn⟩
  · have r1 : (s'.gpr .x0).setWidth 32 = 1 := by rw [h0]; rfl
    exact ⟨fun _ => red, outcome_of_min (.inl ⟨r1, hs⟩)⟩
  · have r0 : (s'.gpr .x0).setWidth 32 = 0 := by rw [h0]; rfl
    refine ⟨fun h => ?_, outcome_of_min (.inr ⟨r0, hn⟩)⟩
    rw [r0] at h; cases h

/-! ## Constant time -/

/-- The bytes of a polynomial of zeros are zero. -/
theorem byte_zero {m : Mem} {p : Addr} (h : ∀ i < 256, coeffAt m p i = 0) {y : Addr}
    (hy : (polyRegion p).Contains y 1) : m y = 0 := by
  simp only [Region.Contains] at hy
  have e : y = coeffAddr p ((y - p).toNat / 4) + BitVec.ofNat 64 ((y - p).toNat % 4) := by
    rw [coeffAddr, ptr_add, show 4 * ((y - p).toNat / 4) + (y - p).toNat % 4 = (y - p).toNat by omega]
    bv_omega
  rw [e, Mem.readW_byte m _ (by omega), ← coeffAt_eq, h _ (by omega)]
  ext i hi
  simp

/-- A byte of a region, at its offset. -/
theorem at_off {b y : Addr} {len : Nat} (hy : (⟨b, len⟩ : Region).Contains y 1) :
    ∃ p < len, y = b + BitVec.ofNat 64 p := by
  simp only [Region.Contains] at hy
  exact ⟨(y - b).toNat, by omega, by bv_omega⟩

/-- The loop's regions. -/
abbrev lrd (N : Nat) (bP : Addr) : List Region := [⟨bP, 3 * N⟩]
abbrev lwr (aP : Addr) : List Region := [polyRegion aP]

theorem LPre.narrow {N : Nat} {B : List Byte} {bP aP : Addr} {s : State} (h : VG.Proof.MlKem.AArch64.Sample.LPre N B bP aP s) :
    VG.Proof.MlKem.AArch64.Sample.LPre N B bP aP (s.withRegions (VG.Proof.MlKem.AArch64.Sample.lrd N bP) (VG.Proof.MlKem.AArch64.Sample.lwr aP)) :=
  ⟨h.buf, fun p hp => in_rd (in_regions (List.mem_singleton_self _)
      (contains_off (by omega) (by have := h.bound; omega))),
    fun i hi => in_regions (List.mem_singleton_self _) (coeff_contains _ (show i < n from hi)),
    h.disj, h.zero, h.x2, h.x3, h.x4, h.x5, h.x9, h.x10, h.bound⟩

/-- Two runs of the loop from the same output and zeros agree on what
`memTaint` tracks. -/
theorem iters_agree {N : Nat} {B : List Byte} {bP aP : Addr} {u₁ u₂ : State}
    (h₁ : VG.Proof.MlKem.AArch64.Sample.LPre N B bP aP u₁) (h₂ : VG.Proof.MlKem.AArch64.Sample.LPre N B bP aP u₂) (hsp : u₁.sp = u₂.sp) :
    memTaint.Agree (Taint.ofRegs [.x2, .x3, .x4, .x5, .x9, .x10]) (u₁.withRegions (VG.Proof.MlKem.AArch64.Sample.lrd N bP) (VG.Proof.MlKem.AArch64.Sample.lwr aP))
      (u₂.withRegions (VG.Proof.MlKem.AArch64.Sample.lrd N bP) (VG.Proof.MlKem.AArch64.Sample.lwr aP)) := by
  have n4 : ∀ {a b : BitVec 64} {k : Nat}, a.toNat = k → b.toNat = k → a = b :=
    fun ha hb => BitVec.eq_of_toNat_eq (ha.trans hb.symm)
  refine ⟨agree_of (by simp only [State.withRegions_sp]; exact hsp) fun r hr => ?_, rfl, rfl,
    fun y hy => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [State.withRegions_gpr]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h₁.x2, h₂.x2]
    · rw [h₁.x3, h₂.x3]
    · exact n4 h₁.x4 h₂.x4
    · exact n4 h₁.x5 h₂.x5
    · exact n4 h₁.x9 h₂.x9
    · exact n4 h₁.x10 h₂.x10
  · simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem] at hy ⊢
    obtain ⟨R, hR, hc⟩ := hy
    rcases VG.Proof.MlKem.AArch64.Sample.mem2 hR with rfl | rfl
    · obtain ⟨p, hp, rfl⟩ := VG.Proof.MlKem.AArch64.Sample.at_off hc
      rw [h₁.buf p hp, h₂.buf p hp]
    · rw [VG.Proof.MlKem.AArch64.Sample.byte_zero h₁.zero hc, VG.Proof.MlKem.AArch64.Sample.byte_zero h₂.zero hc]

/-- The loop's regions are the parts of `scratch` and `a` it uses. -/
theorem covers_loop {σ u : State} (hp : VG.Proof.MlKem.AArch64.Sample.Pre σ) {N : Nat} (hN : N ≤ 280) (hrd : u.rd = σ.rd)
    (hwr : u.wr = σ.wr) :
    Covers (VG.Proof.MlKem.AArch64.Sample.lrd N (VG.Proof.MlKem.AArch64.Sample.So σ 0) ++ VG.Proof.MlKem.AArch64.Sample.lwr (VG.Proof.MlKem.AArch64.Sample.aP σ)) (u.rd ++ u.wr) ∧ Covers (VG.Proof.MlKem.AArch64.Sample.lwr (VG.Proof.MlKem.AArch64.Sample.aP σ)) u.wr := by
  rw [hrd, hwr, hp.rd, hp.wr]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · rcases VG.Proof.MlKem.AArch64.Sample.mem2 hr with rfl | rfl
    · exact ⟨VG.Proof.MlKem.AArch64.Sample.scR σ, by simp, 0, rfl, by show 0 + 3 * N ≤ 2048; omega⟩
    · exact ⟨VG.Proof.MlKem.AArch64.Sample.aR σ, by simp, 0, (ptr_zero _).symm, Nat.le_of_ble_eq_true rfl⟩
  · rw [List.mem_singleton.mp hr]
    exact ⟨VG.Proof.MlKem.AArch64.Sample.aR σ, by simp, 0, (ptr_zero _).symm, Nat.le_of_ble_eq_true rfl⟩

/-- The loop of `SampleNTT`, in two runs from the same output and zeros. -/
theorem loop_ct {N : Nat} {B : List Byte} {bP aP : Addr} {c : Prog isa} {P : State → State → Prop}
    (hl : ∀ s₁ s₂, P s₁ s₂ → VG.Proof.MlKem.AArch64.Sample.LPre N B bP aP s₁ ∧ VG.Proof.MlKem.AArch64.Sample.LPre N B bP aP s₂ ∧ s₁.sp = s₂.sp)
    (hc : ∀ s₁ s₂, P s₁ s₂ → (Covers (VG.Proof.MlKem.AArch64.Sample.lrd N bP ++ VG.Proof.MlKem.AArch64.Sample.lwr aP) (s₁.rd ++ s₁.wr) ∧ Covers (VG.Proof.MlKem.AArch64.Sample.lwr aP) s₁.wr) ∧
      (Covers (VG.Proof.MlKem.AArch64.Sample.lrd N bP ++ VG.Proof.MlKem.AArch64.Sample.lwr aP) (s₂.rd ++ s₂.wr) ∧ Covers (VG.Proof.MlKem.AArch64.Sample.lwr aP) s₂.wr))
    (hx : ∀ {u}, VG.Proof.MlKem.AArch64.Sample.LPre N B bP aP u → ∃ t u', Exec isa c u t u')
    (ht : ∃ hint : Taint.Hint memTaint.T,
      (memTaint.check (Taint.ofRegs [.x2, .x3, .x4, .x5, .x9, .x10]) c hint).isSome = true) :
    RelCT isa P c fun _ _ => True := by
  obtain ⟨_, ht⟩ := ht
  refine RelCT.narrow (VG.Proof.MlKem.AArch64.Sample.lrd N bP) (VG.Proof.MlKem.AArch64.Sample.lwr aP) hc (fun s₁ s₂ h => ?_)
    (RelCT.taint (A := VG.AArch64.memTaint) (Taint.ofRegs [.x2, .x3, .x4, .x5, .x9, .x10])
      (fun _ _ h => ?_) ht)
  · obtain ⟨l₁, l₂, -⟩ := hl s₁ s₂ h
    exact ⟨hx l₁.narrow, hx l₂.narrow⟩
  · obtain ⟨s₁, s₂, hP, rfl, rfl⟩ := h
    obtain ⟨l₁, l₂, hsp⟩ := hl s₁ s₂ hP
    exact VG.Proof.MlKem.AArch64.Sample.iters_agree l₁ l₂ hsp

theorem loop_taint : ∃ hint : Taint.Hint memTaint.T,
    (memTaint.check (Taint.ofRegs [.x2, .x3, .x4, .x5, .x9, .x10]) sampleLoop hint).isSome = true :=
  ⟨_, by taint_decide⟩

theorem iters_taint : ∃ hint : Taint.Hint memTaint.T,
    (memTaint.check (Taint.ofRegs [.x2, .x3, .x4, .x5, .x9, .x10]) (.loop sampleBody (.nonzero .x .x5))
      hint).isSome = true :=
  ⟨_, by taint_decide⟩

/-- What each run of `sampleFull` knows after the Keccak calls. -/
abbrev FA (σ u : State) : Prop := VG.Proof.MlKem.AArch64.Sample.LPre 280 (VG.Proof.MlKem.AArch64.Sample.Bs σ) (VG.Proof.MlKem.AArch64.Sample.So σ 0) (VG.Proof.MlKem.AArch64.Sample.aP σ) u ∧ VG.Proof.MlKem.AArch64.Sample.Fin σ u

theorem full_ct (v : Proof.Sha3.AArch64.Permutation) : ConstantTime isa sampleAArch64.pre sampleAArch64.pub (sampleFullWith v.callee) := by
  obtain ⟨hint, hhint⟩ := v.sampleFullTaint
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.seq
    ((VectorTaint.relCT (Taint.ofRegs [.x0, .x1, .x2])
      (fun _ _ h => agree_of h.2.2.2.2.2.1 (by
        obtain ⟨-, -, e0, e1, e2, -, -⟩ := h
        simp [e0, e1, e2])) hhint).wpDep (F := VG.Proof.MlKem.AArch64.Sample.FA)
      fun s₁ s₂ h => ⟨(VG.Proof.MlKem.AArch64.Sample.phaseA_ok v) (VG.Proof.MlKem.AArch64.Sample.pre_of h.1), (VG.Proof.MlKem.AArch64.Sample.phaseA_ok v) (VG.Proof.MlKem.AArch64.Sample.pre_of h.2.1)⟩) ?_)
  refine RelCT.mono (RelCT.exists_ (P := fun (x : Addr × Addr × List Byte) s₁ s₂ =>
      ∃ σ₁ σ₂, (sampleAArch64.pre σ₁ ∧ sampleAArch64.pre σ₂ ∧ sampleAArch64.pub σ₁ σ₂) ∧ VG.Proof.MlKem.AArch64.Sample.FA σ₁ s₁ ∧
        VG.Proof.MlKem.AArch64.Sample.FA σ₂ s₂ ∧ VG.Proof.MlKem.AArch64.Sample.So σ₁ 0 = x.1 ∧ VG.Proof.MlKem.AArch64.Sample.aP σ₁ = x.2.1 ∧ VG.Proof.MlKem.AArch64.Sample.Bs σ₁ = x.2.2)
    fun x => VG.Proof.MlKem.AArch64.Sample.loop_ct (N := 280) (B := x.2.2) (bP := x.1) (aP := x.2.1) (fun s₁ s₂ h => ?_)
      (fun s₁ s₂ h => ?_) (fun hl => by obtain ⟨t, u, e, -⟩ := VG.Proof.MlKem.AArch64.Sample.loop_ok hl; exact ⟨t, u, e⟩) VG.Proof.MlKem.AArch64.Sample.loop_taint)
    (fun s₁ s₂ h => ?_) fun _ _ h => h
  · obtain ⟨σ₁, σ₂, ⟨-, -, -, e1, e2, esp, eB⟩, ⟨l₁, f₁⟩, ⟨l₂, f₂⟩, x1, x2, x3⟩ := h
    rw [← x1, ← x2, ← x3]
    rw [show VG.Proof.MlKem.AArch64.Sample.So σ₂ 0 = VG.Proof.MlKem.AArch64.Sample.So σ₁ 0 by rw [VG.Proof.MlKem.AArch64.Sample.So, VG.Proof.MlKem.AArch64.Sample.So, VG.Proof.MlKem.AArch64.Sample.scP, VG.Proof.MlKem.AArch64.Sample.scP, e2], show VG.Proof.MlKem.AArch64.Sample.aP σ₂ = VG.Proof.MlKem.AArch64.Sample.aP σ₁ from e1.symm,
      show VG.Proof.MlKem.AArch64.Sample.Bs σ₂ = VG.Proof.MlKem.AArch64.Sample.Bs σ₁ from (map_toNat_inj eB).symm] at l₂
    exact ⟨l₁, l₂, by rw [f₁.sp, f₂.sp, esp]⟩
  · obtain ⟨σ₁, σ₂, ⟨p₁, p₂, -, e1, e2, -, -⟩, ⟨-, f₁⟩, ⟨-, f₂⟩, x1, x2, -⟩ := h
    rw [← x1, ← x2]
    have c₂ := VG.Proof.MlKem.AArch64.Sample.covers_loop (VG.Proof.MlKem.AArch64.Sample.pre_of p₂) (N := 280) (by decide) f₂.rd f₂.wr
    rw [show VG.Proof.MlKem.AArch64.Sample.So σ₂ 0 = VG.Proof.MlKem.AArch64.Sample.So σ₁ 0 by rw [VG.Proof.MlKem.AArch64.Sample.So, VG.Proof.MlKem.AArch64.Sample.So, VG.Proof.MlKem.AArch64.Sample.scP, VG.Proof.MlKem.AArch64.Sample.scP, e2], show VG.Proof.MlKem.AArch64.Sample.aP σ₂ = VG.Proof.MlKem.AArch64.Sample.aP σ₁ from e1.symm] at c₂
    exact ⟨VG.Proof.MlKem.AArch64.Sample.covers_loop (VG.Proof.MlKem.AArch64.Sample.pre_of p₁) (by decide) f₁.rd f₁.wr, c₂⟩
  · obtain ⟨-, σ₁, σ₂, hP, f₁, f₂⟩ := h
    exact ⟨(VG.Proof.MlKem.AArch64.Sample.So σ₁ 0, VG.Proof.MlKem.AArch64.Sample.aP σ₁, VG.Proof.MlKem.AArch64.Sample.Bs σ₁), σ₁, σ₂, hP, f₁, f₂, rfl, rfl, rfl⟩

/-- Constant time from any two states related by `P`, proved for each pair. -/
theorem RelCT.pointwise {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ s₁ s₂, P s₁ s₂ → RelCT isa (fun a b => a = s₁ ∧ b = s₂) c Q) : RelCT isa P c Q :=
  fun s₁ s₂ _ _ _ _ hp e₁ e₂ => h s₁ s₂ hp s₁ s₂ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂

theorem ct (v : Proof.Sha3.AArch64.Permutation) : ConstantTime isa sampleAArch64.pre sampleAArch64.pub (sampleNTTWith v.callee) := by
  obtain ⟨hint, hhint⟩ := v.sampleFastTaint
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.pointwise fun σ₁ σ₂ hσ => ?_)
  obtain ⟨p₁, p₂, e0, e1, e2, esp, eB⟩ := hσ
  have hB : VG.Proof.MlKem.AArch64.Sample.Bs σ₂ = VG.Proof.MlKem.AArch64.Sample.Bs σ₁ := (map_toNat_inj eB).symm
  have q₁ := VG.Proof.MlKem.AArch64.Sample.pre_of p₁
  have q₂ := VG.Proof.MlKem.AArch64.Sample.pre_of p₂
  have eS : VG.Proof.MlKem.AArch64.Sample.So σ₂ 0 = VG.Proof.MlKem.AArch64.Sample.So σ₁ 0 := by rw [VG.Proof.MlKem.AArch64.Sample.So, VG.Proof.MlKem.AArch64.Sample.So, VG.Proof.MlKem.AArch64.Sample.scP, VG.Proof.MlKem.AArch64.Sample.scP, e2]
  have eA : VG.Proof.MlKem.AArch64.Sample.aP σ₂ = VG.Proof.MlKem.AArch64.Sample.aP σ₁ := e1.symm
  have e26 : VG.Proof.MlKem.AArch64.Sample.scP σ₂ = VG.Proof.MlKem.AArch64.Sample.scP σ₁ := e2.symm
  -- the output of `(sampleFastWith v.callee)`, and its loop
  refine RelCT.seq (RelCT.seq (R := fun a b => (VG.Proof.MlKem.AArch64.Sample.LPre 168 (VG.Proof.MlKem.AArch64.Sample.Bs σ₁) (VG.Proof.MlKem.AArch64.Sample.So σ₁ 0) (VG.Proof.MlKem.AArch64.Sample.aP σ₁) a ∧ VG.Proof.MlKem.AArch64.Sample.MidA σ₁ a) ∧
      (VG.Proof.MlKem.AArch64.Sample.LPre 168 (VG.Proof.MlKem.AArch64.Sample.Bs σ₂) (VG.Proof.MlKem.AArch64.Sample.So σ₂ 0) (VG.Proof.MlKem.AArch64.Sample.aP σ₂) b ∧ VG.Proof.MlKem.AArch64.Sample.MidA σ₂ b))
    (RelCT.mono ((VectorTaint.relCT (P := fun a b => a = σ₁ ∧ b = σ₂) (Taint.ofRegs [.x0, .x1, .x2])
      (fun a b h => by
        obtain ⟨rfl, rfl⟩ := h
        exact agree_of esp (by simp [e0, e1, e2])) hhint).wp
      (F₁ := fun a => VG.Proof.MlKem.AArch64.Sample.LPre 168 (VG.Proof.MlKem.AArch64.Sample.Bs σ₁) (VG.Proof.MlKem.AArch64.Sample.So σ₁ 0) (VG.Proof.MlKem.AArch64.Sample.aP σ₁) a ∧ VG.Proof.MlKem.AArch64.Sample.MidA σ₁ a)
      (F₂ := fun b => VG.Proof.MlKem.AArch64.Sample.LPre 168 (VG.Proof.MlKem.AArch64.Sample.Bs σ₂) (VG.Proof.MlKem.AArch64.Sample.So σ₂ 0) (VG.Proof.MlKem.AArch64.Sample.aP σ₂) b ∧ VG.Proof.MlKem.AArch64.Sample.MidA σ₂ b)
      fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨(VG.Proof.MlKem.AArch64.Sample.fastA_ok v) q₁, (VG.Proof.MlKem.AArch64.Sample.fastA_ok v) q₂⟩)
      (fun _ _ h => h) fun _ _ h => h.2)
    (RelCT.mono ((VG.Proof.MlKem.AArch64.Sample.loop_ct (N := 168) (B := VG.Proof.MlKem.AArch64.Sample.Bs σ₁) (bP := VG.Proof.MlKem.AArch64.Sample.So σ₁ 0) (aP := VG.Proof.MlKem.AArch64.Sample.aP σ₁) (fun a b h => ?_)
      (fun a b h => ?_) (fun hl => by obtain ⟨t, u, e, -⟩ := VG.Proof.MlKem.AArch64.Sample.iters_ok (by decide) hl; exact ⟨t, u, e⟩)
      VG.Proof.MlKem.AArch64.Sample.iters_taint).wp (F₁ := VG.Proof.MlKem.AArch64.Sample.FastPost σ₁) (F₂ := VG.Proof.MlKem.AArch64.Sample.FastPost σ₂)
      fun a b h => ⟨VG.Proof.MlKem.AArch64.Sample.fastLoop_ok q₁ h.1.1 h.1.2, VG.Proof.MlKem.AArch64.Sample.fastLoop_ok q₂ h.2.1 h.2.2⟩)
      (fun _ _ h => h) fun _ _ h => h.2)) ?_
  · obtain ⟨⟨l₁, m₁⟩, ⟨l₂, m₂⟩⟩ := h
    rw [hB, eS, eA] at l₂
    exact ⟨l₁, l₂, by rw [m₁.sp, m₂.sp, esp]⟩
  · obtain ⟨⟨-, m₁⟩, ⟨-, m₂⟩⟩ := h
    have c₂ := VG.Proof.MlKem.AArch64.Sample.covers_loop q₂ (N := 168) (by decide) m₂.rd m₂.wr
    rw [eS, eA] at c₂
    exact ⟨VG.Proof.MlKem.AArch64.Sample.covers_loop q₁ (by decide) m₁.rd m₁.wr, c₂⟩
  -- whether it is done
  refine RelCT.ite (fun a b h => ?_) (RelCT.mono (RelCT.taint (A := taint) (Taint.ofRegs [.x26])
      (fun a b h => agree_of (by rw [h.1.1.mid.sp, h.1.2.mid.sp, esp])
        (by simp [h.1.1.mid.x26, h.1.2.mid.x26, e26])) (by taint_decide)) (fun _ _ h => h) fun _ _ h => h)
    (RelCT.seq (RelCT.mono ((RelCT.taint (A := taint) (Taint.ofRegs [.x26])
      (fun a b h => agree_of (by rw [h.1.1.mid.sp, h.1.2.mid.sp, esp])
        (by simp [h.1.1.mid.x26, h.1.2.mid.x26, e26])) (by taint_decide)).wp
      (F₁ := VG.Proof.MlKem.AArch64.Sample.RetryPost σ₁) (F₂ := VG.Proof.MlKem.AArch64.Sample.RetryPost σ₂)
      fun a b h => ⟨VG.Proof.MlKem.AArch64.Sample.retryBlock_ok q₁ h.1.1, VG.Proof.MlKem.AArch64.Sample.retryBlock_ok q₂ h.1.2⟩) (fun _ _ h => h)
      fun _ _ h => h.2) ?_)
  · obtain ⟨h₁, h₂⟩ := h
    rw [VG.Proof.MlKem.AArch64.eval_zero, VG.Proof.MlKem.AArch64.eval_zero]
    have v : a.gpr .x4 = b.gpr .x4 := BitVec.eq_of_toNat_eq (by rw [h₁.x4, h₂.x4, hB])
    rw [v]
  · -- `(sampleFullWith v.callee)`, from states that satisfy its contract
    refine fun a b t₁ t₂ a' b' h e₁ e₂ => ⟨(VG.Proof.MlKem.AArch64.Sample.full_ct v) a b t₁ t₂ a' b' (h.1.pre q₁) (h.2.pre q₂) ?_ e₁ e₂, trivial⟩
    obtain ⟨h₁, h₂⟩ := h
    refine ⟨by rw [h₁.x0, h₂.x0, VG.Proof.MlKem.AArch64.Sample.sdP, VG.Proof.MlKem.AArch64.Sample.sdP, e0], by rw [h₁.x1, h₂.x1, eA], by rw [h₁.x2, h₂.x2, e26],
      by rw [h₁.sp, h₂.sp, esp], ?_⟩
    rw [h₁.x0, h₂.x0, h₁.seed, h₂.seed, hB]

/-! ## Verified -/

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 34⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem sample_correctWith (v : Proof.Sha3.AArch64.Permutation) (s : State) (hs : sampleAArch64.pre s) :
    ∃ t s', Exec isa (sampleNTTWith v.callee) s t s' ∧ abiPreserved s s' ∧ sampleAArch64.post s s' :=
  (VG.Proof.MlKem.AArch64.Sample.correct v) (VG.Proof.MlKem.AArch64.Sample.pre_of hs)

/-- What callers use: `a` is always reduced, and the return value is
determined by the seed (`SampleNTT` with 280 iterations). -/
def sampleStrong : Contract isa :=
  { VG.Proof.MlKem.sampleAArch64 with
    post := fun s s' => Reduced s'.mem (s.gpr .x1) ∧
      ((s'.gpr .x0 = 1 ∧ sampleNTT 280 (bytesAt s.mem (s.gpr .x0) 34) = some (polyAt s'.mem (s.gpr .x1))) ∨
        (s'.gpr .x0 = 0 ∧ sampleNTT 280 (bytesAt s.mem (s.gpr .x0) 34) = none)) }

theorem sample_strongWith (v : Proof.Sha3.AArch64.Permutation) (s : State) (hs : sampleStrong.pre s) :
    ∃ t s', Exec isa (sampleNTTWith v.callee) s t s' ∧ abiPreserved s s' ∧ sampleStrong.post s s' :=
  WP.mono ((VG.Proof.MlKem.AArch64.Sample.strong_ok v) (VG.Proof.MlKem.AArch64.Sample.pre_of hs)) fun _ h => h

theorem ct_strongWith (v : Proof.Sha3.AArch64.Permutation) : ConstantTime isa sampleStrong.pre sampleStrong.pub (sampleNTTWith v.callee) := (VG.Proof.MlKem.AArch64.Sample.ct v)

theorem sample_verifiedWith (v : Proof.Sha3.AArch64.Permutation) :
    Verified AArch64.target (sampleNTTWith v.callee) (Spec.MlKem.sampleNTTContract AArch64.abi 16) :=
  Verified.of_correct (VG.Proof.MlKem.AArch64.Sample.sample_correctWith v) (VG.Proof.MlKem.AArch64.Sample.ct v) (by
    mlkem_implies [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, VG.Proof.MlKem.sampleAArch64,
      AArch64.abi, AArch64.argRegs] [sat] using VG.Proof.MlKem.AArch64.Sample.sat)

theorem sample_correct (s : State) (hs : sampleAArch64.pre s) :
    ∃ t s', Exec isa sampleNTT s t s' ∧ abiPreserved s s' ∧ sampleAArch64.post s s' :=
  VG.Proof.MlKem.AArch64.Sample.sample_correctWith .scalar s hs

theorem sample_strong (s : State) (hs : sampleStrong.pre s) :
    ∃ t s', Exec isa sampleNTT s t s' ∧ abiPreserved s s' ∧ sampleStrong.post s s' :=
  VG.Proof.MlKem.AArch64.Sample.sample_strongWith .scalar s hs

theorem ct_strong : ConstantTime isa sampleStrong.pre sampleStrong.pub sampleNTT :=
  VG.Proof.MlKem.AArch64.Sample.ct_strongWith .scalar

theorem sample_verified :
    Verified AArch64.target sampleNTT (Spec.MlKem.sampleNTTContract AArch64.abi 16) :=
  VG.Proof.MlKem.AArch64.Sample.sample_verifiedWith .scalar

end VG.Proof.MlKem.AArch64.Sample

end
