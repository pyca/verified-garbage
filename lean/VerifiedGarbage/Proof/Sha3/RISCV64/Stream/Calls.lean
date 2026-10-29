module

public import VerifiedGarbage.Proof.Sha3.RISCV64.Contract
public import VerifiedGarbage.Impl.Sha3.RISCV64.Stream
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Verified
import VerifiedGarbage.Proof.Sha3.RISCV64.Stream.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The SHA-3 sponge on RISC-V: calling it

As PPC64LE's (`Proof/MlKem/PPC64LE/KCall.lean`): calls of
`vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze` from their
callers' proofs (`WP.callAny`, their frames and the permutation's using the
1168 bytes below the stack pointer): the callee's precondition on entry
(`absorb_pre`, `pad_pre`, `squeeze_pre`), and what holds when it returns
(`absorb_call`, `pad_call`, `squeeze_call`). They keep `s0`, `s1` and
`s7`–`s11` untouched, and save and restore `s2`–`s6`.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Stream

open VG VG.RISCV64
open VG.Spec.Sha3 (stateAt bytesAt absorb pad rates squeezeFrom)

theorem absorb_sdepth : sdepth Impl.Sha3.RISCV64.Stream.absorb ≤ 1168 := by lit_decide
theorem pad_sdepth : sdepth Impl.Sha3.RISCV64.Stream.pad ≤ 1168 := by lit_decide
theorem squeeze_sdepth : sdepth Impl.Sha3.RISCV64.Stream.squeeze ≤ 1168 := by lit_decide

theorem rate_lt {rate : Nat} (h : rate ∈ rates) : rate < 2 ^ 64 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem ofNat_toNat' {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ce_gpr (s : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (s.callEntry.withRegions rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

/-- A call of code with frames within the 1168 bytes below the stack pointer. -/
theorem call1168 {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hd : sdepth c ≤ 1168) {s : State} {rd wr : List Region} (hpre : k.pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame (wr ++ [below s.sp 1168]) s.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      k.post (s.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s') :
    WP isa (.call n c) s Q :=
  WP.callAny hv hpre hc hw (fun s' hrd hwr hsp hf hcs hpost => hQ s' hrd hwr hsp (hf.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub hd (by decide)⟩) hcs hpost)
    (by omega)

/-! ## `vg_keccak_absorb` -/

section
variable {s : State} {st dp : Addr} {rate pos len : Nat}

/-- The facts a call of `vg_keccak_absorb(st, rate, pos, dp, len)` needs. -/
structure AbsorbArgs (s : State) (st dp : Addr) (rate pos len : Nat) : Prop where
  a0 : s.gpr .a0 = st
  a1 : s.gpr .a1 = BitVec.ofNat 64 rate
  a2 : s.gpr .a2 = BitVec.ofNat 64 pos
  a3 : s.gpr .a3 = dp
  a4 : s.gpr .a4 = BitVec.ofNat 64 len
  hrate : rate ∈ rates
  hpos : pos < rate
  hlen : len < 2 ^ 64
  al : s.sp.toNat % 16 = 0
  sp : 1168 ≤ s.sp.toNat
  d_st : Region.Disjoint ⟨dp, len⟩ ⟨st, 200⟩
  k_st : (below s.sp 1168).Disjoint ⟨st, 200⟩
  k_d : (below s.sp 1168).Disjoint ⟨dp, len⟩

theorem absorb_pre (h : AbsorbArgs s st dp rate pos len) :
    Proof.Sha3.absorbRISCV64.pre (s.callEntry.withRegions [⟨dp, len⟩] [⟨st, 200⟩]) := by
  have hr := rate_lt h.hrate
  simp only [Proof.Sha3.absorbRISCV64, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, ce_gpr s _ _ (by decide : Reg.a0 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.a1 ∉ linkRegs),
    ce_gpr s _ _ (by decide : Reg.a2 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.a3 ∉ linkRegs),
    ce_gpr s _ _ (by decide : Reg.a4 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, h.a4, ofNat_toNat' h.hlen,
    ofNat_toNat' hr, ofNat_toNat' (Nat.lt_trans h.hpos hr)]
  exact ⟨trivial, trivial, h.d_st, h.al, h.sp, h.k_st, h.k_d, h.hrate, h.hpos⟩

theorem absorb_call (h : AbsorbArgs s st dp rate pos len)
    (hc : Covers ([⟨dp, len⟩] ++ [⟨st, 200⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, below s.sp 1168] s.mem s'.mem →
      (∀ msg, Spec.Sha3.Repr s.mem st rate msg → pos = msg.length % rate →
        Spec.Sha3.Repr s'.mem st rate (msg ++ bytesAt s.mem dp len)) →
      (s'.gpr .a0).toNat = (pos + len) % rate → Q s') :
    WP isa (.call Spec.Sha3.absorbApi.name Impl.Sha3.RISCV64.Stream.absorb) s Q := by
  have hr := rate_lt h.hrate
  refine call1168 (k := Proof.Sha3.absorbRISCV64) absorb_verified'.1 absorb_sdepth
    (absorb_pre h) hc hw fun s' hrd hwr hsp hf hcs hpost => ?_
  simp only [Proof.Sha3.absorbRISCV64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    ce_gpr s _ _ (by decide : Reg.a0 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.a1 ∉ linkRegs),
    ce_gpr s _ _ (by decide : Reg.a2 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.a3 ∉ linkRegs),
    ce_gpr s _ _ (by decide : Reg.a4 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, h.a4, ofNat_toNat' h.hlen,
    ofNat_toNat' hr, ofNat_toNat' (Nat.lt_trans h.hpos hr)] at hpost
  exact hQ s' hrd hwr hsp hcs (by simpa using hf) hpost.1 hpost.2

end

/-! ## `vg_keccak_pad` -/

section
variable {s : State} {st : Addr} {rate pos : Nat}

/-- The facts a call of `vg_keccak_pad(st, rate, pos, suffix)` needs. -/
structure PadArgs (s : State) (st : Addr) (rate pos : Nat) : Prop where
  a0 : s.gpr .a0 = st
  a1 : s.gpr .a1 = BitVec.ofNat 64 rate
  a2 : s.gpr .a2 = BitVec.ofNat 64 pos
  hrate : rate ∈ rates
  hpos : pos < rate
  al : s.sp.toNat % 16 = 0
  sp : 1168 ≤ s.sp.toNat
  k_st : (below s.sp 1168).Disjoint ⟨st, 200⟩

theorem pad_pre (h : PadArgs s st rate pos) :
    Proof.Sha3.padRISCV64.pre (s.callEntry.withRegions [] [⟨st, 200⟩]) := by
  have hr := rate_lt h.hrate
  simp only [Proof.Sha3.padRISCV64, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, ce_gpr s _ _ (by decide : Reg.a0 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.a1 ∉ linkRegs),
    ce_gpr s _ _ (by decide : Reg.a2 ∉ linkRegs), h.a0, h.a1, h.a2, ofNat_toNat' hr,
    ofNat_toNat' (Nat.lt_trans h.hpos hr)]
  exact ⟨trivial, trivial, h.al, by omega_using [h.sp], h.k_st.sub_left (below_sub (by decide) (by decide)),
    h.hrate, h.hpos⟩

theorem pad_call (h : PadArgs s st rate pos)
    (hc : Covers ([] ++ [⟨st, 200⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, below s.sp 1168] s.mem s'.mem →
      (∀ msg, Spec.Sha3.Repr s.mem st rate msg → pos = msg.length % rate →
        stateAt s'.mem st = absorb rate (pad rate ((s.gpr .a3).setWidth 8) msg)) → Q s') :
    WP isa (.call Spec.Sha3.padApi.name Impl.Sha3.RISCV64.Stream.pad) s Q := by
  have hr := rate_lt h.hrate
  refine call1168 (k := Proof.Sha3.padRISCV64) pad_verified'.1 pad_sdepth
    (pad_pre h) hc hw fun s' hrd hwr hsp hf hcs hpost => ?_
  simp only [Proof.Sha3.padRISCV64, State.withRegions_mem, State.callEntry_mem,
    ce_gpr s _ _ (by decide : Reg.a0 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.a1 ∉ linkRegs),
    ce_gpr s _ _ (by decide : Reg.a2 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.a3 ∉ linkRegs), h.a0, h.a1, h.a2,
    ofNat_toNat' hr, ofNat_toNat' (Nat.lt_trans h.hpos hr)] at hpost
  exact hQ s' hrd hwr hsp hcs (by simpa using hf) hpost

end

/-! ## `vg_keccak_squeeze` -/

section
variable {s : State} {st op : Addr} {rate pos len : Nat}

/-- The facts a call of `vg_keccak_squeeze(st, rate, pos, op, len)` needs. -/
structure SqueezeArgs (s : State) (st op : Addr) (rate pos len : Nat) : Prop where
  a0 : s.gpr .a0 = st
  a1 : s.gpr .a1 = BitVec.ofNat 64 rate
  a2 : s.gpr .a2 = BitVec.ofNat 64 pos
  a3 : s.gpr .a3 = op
  a4 : s.gpr .a4 = BitVec.ofNat 64 len
  hrate : rate ∈ rates
  hpos : pos ≤ rate
  hlen : len < 2 ^ 64
  al : s.sp.toNat % 16 = 0
  sp : 1168 ≤ s.sp.toNat
  st_o : Region.Disjoint ⟨st, 200⟩ ⟨op, len⟩
  k_st : (below s.sp 1168).Disjoint ⟨st, 200⟩
  k_o : (below s.sp 1168).Disjoint ⟨op, len⟩

theorem squeeze_pre (h : SqueezeArgs s st op rate pos len) :
    Proof.Sha3.squeezeRISCV64.pre (s.callEntry.withRegions [] [⟨st, 200⟩, ⟨op, len⟩]) := by
  have hr := rate_lt h.hrate
  simp only [Proof.Sha3.squeezeRISCV64, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, ce_gpr s _ _ (by decide : Reg.a0 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.a1 ∉ linkRegs),
    ce_gpr s _ _ (by decide : Reg.a2 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.a3 ∉ linkRegs),
    ce_gpr s _ _ (by decide : Reg.a4 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, h.a4, ofNat_toNat' h.hlen,
    ofNat_toNat' hr, ofNat_toNat' (Nat.lt_of_le_of_lt h.hpos hr)]
  exact ⟨trivial, trivial, h.st_o, h.al, h.sp, h.k_st, h.k_o, h.hrate, h.hpos⟩

theorem squeeze_call (h : SqueezeArgs s st op rate pos len)
    (hc : Covers ([] ++ [⟨st, 200⟩, ⟨op, len⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨op, len⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨op, len⟩, below s.sp 1168] s.mem s'.mem →
      bytesAt s'.mem op len = squeezeFrom rate (stateAt s.mem st) pos len →
      (s'.gpr .a0).toNat ≤ rate →
      (∀ d, squeezeFrom rate (stateAt s'.mem st) (s'.gpr .a0).toNat d =
        squeezeFrom rate (stateAt s.mem st) (pos + len) d) → Q s') :
    WP isa (.call Spec.Sha3.squeezeApi.name Impl.Sha3.RISCV64.Stream.squeeze) s Q := by
  have hr := rate_lt h.hrate
  refine call1168 (k := Proof.Sha3.squeezeRISCV64) squeeze_verified'.1 squeeze_sdepth
    (squeeze_pre h) hc hw fun s' hrd hwr hsp hf hcs hpost => ?_
  simp only [Proof.Sha3.squeezeRISCV64, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    ce_gpr s _ _ (by decide : Reg.a0 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.a1 ∉ linkRegs),
    ce_gpr s _ _ (by decide : Reg.a2 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.a3 ∉ linkRegs),
    ce_gpr s _ _ (by decide : Reg.a4 ∉ linkRegs), h.a0, h.a1, h.a2, h.a3, h.a4, ofNat_toNat' h.hlen,
    ofNat_toNat' hr, ofNat_toNat' (Nat.lt_of_le_of_lt h.hpos hr)] at hpost
  exact hQ s' hrd hwr hsp hcs (by simpa using hf) hpost.1 hpost.2.1 hpost.2.2

end

end VG.Proof.Sha3.RISCV64.Stream
