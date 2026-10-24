module

public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.Sha3.PPC64LE.Contract
public import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Verified

/-!
# ML-KEM on PPC64LE: calling the SHA-3 sponge

As on x86-64 (`Proof/MlKem/X86_64/KCall.lean`): calls of
`vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze` from their
proofs (`WP.callAny`, their frames using the 48 bytes below the stack
pointer): the callee's precondition on entry (`absorb_pre`, `pad_pre`,
`squeeze_pre`, which the constant-time proofs of callers use too), and what
holds when it returns (`absorb_call`, `pad_call`, `squeeze_call`).
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE

open VG VG.PPC64LE
open VG.Spec.Sha3 (stateAt bytesAt absorb pad rates squeezeFrom)

theorem ce_gpr (s : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (s.callEntry.withRegions rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

theorem rate_lt {rate : Nat} (h : rate ∈ rates) : rate < 2 ^ 64 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem ofNat_toNat' {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- A call of code with frames within the 48 bytes below the stack pointer. -/
theorem call48 {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hd : sdepth c ≤ 48) {s : State} {rd wr : List Region} (hpre : k.pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame (wr ++ [below s.sp 48]) s.mem s'.mem →
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
variable {s : State} {st dp scr : Addr} {rate pos len : Nat}

/-- The facts a call of `vg_keccak_absorb(st, rate, pos, dp, len, scr)` needs. -/
structure AbsorbArgs (s : State) (st dp scr : Addr) (rate pos len : Nat) : Prop where
  r3 : s.gpr .r3 = st
  r4 : s.gpr .r4 = BitVec.ofNat 64 rate
  r5 : s.gpr .r5 = BitVec.ofNat 64 pos
  r6 : s.gpr .r6 = dp
  r7 : s.gpr .r7 = BitVec.ofNat 64 len
  r8 : s.gpr .r8 = scr
  hrate : rate ∈ rates
  hpos : pos < rate
  hlen : len < 2 ^ 64
  sp48 : 48 ≤ s.sp.toNat
  st_scr : Region.Disjoint ⟨st, 200⟩ ⟨scr, 640⟩
  d_st : Region.Disjoint ⟨dp, len⟩ ⟨st, 200⟩
  d_scr : Region.Disjoint ⟨dp, len⟩ ⟨scr, 640⟩
  k_st : (below s.sp 48).Disjoint ⟨st, 200⟩
  k_d : (below s.sp 48).Disjoint ⟨dp, len⟩
  k_scr : (below s.sp 48).Disjoint ⟨scr, 640⟩

theorem absorb_pre (h : AbsorbArgs s st dp scr rate pos len) :
    Proof.Sha3.absorbPPC64LE.pre (s.callEntry.withRegions [⟨dp, len⟩] [⟨st, 200⟩, ⟨scr, 640⟩]) := by
  have hr := rate_lt h.hrate
  simp only [Proof.Sha3.absorbPPC64LE, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, ce_gpr s _ _ (by decide : Reg.r3 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.r4 ∉ linkRegs),
    ce_gpr s _ _ (by decide : Reg.r5 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.r6 ∉ linkRegs),
    ce_gpr s _ _ (by decide : Reg.r7 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.r8 ∉ linkRegs), h.r3, h.r4, h.r5,
    h.r6, h.r7, h.r8, ofNat_toNat' h.hlen, ofNat_toNat' hr, ofNat_toNat' (Nat.lt_trans h.hpos hr)]
  exact ⟨trivial, trivial, h.st_scr, h.d_st, h.d_scr, h.sp48, h.k_st, h.k_d, h.k_scr, h.hrate, h.hpos⟩

theorem absorb_call (h : AbsorbArgs s st dp scr rate pos len)
    (hc : Covers ([⟨dp, len⟩] ++ [⟨st, 200⟩, ⟨scr, 640⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨scr, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨scr, 640⟩, below s.sp 48] s.mem s'.mem →
      (∀ msg, Spec.Sha3.Repr s.mem st rate msg → pos = msg.length % rate →
        Spec.Sha3.Repr s'.mem st rate (msg ++ bytesAt s.mem dp len)) →
      (s'.gpr .r3).toNat = (pos + len) % rate → Q s') :
    WP isa (.call "vg_keccak_absorb_scratch" Impl.Sha3.PPC64LE.Stream.absorb) s Q := by
  have hr := rate_lt h.hrate
  refine call48 (k := Proof.Sha3.absorbPPC64LE) Proof.Sha3.PPC64LE.Stream.absorb_correct Sample.absorb_sdepth
    (absorb_pre h) hc hw fun s' hrd hwr hsp hf hcs hpost => ?_
  simp only [Proof.Sha3.absorbPPC64LE, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    ce_gpr s _ _ (by decide : Reg.r3 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.r4 ∉ linkRegs),
    ce_gpr s _ _ (by decide : Reg.r5 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.r6 ∉ linkRegs),
    ce_gpr s _ _ (by decide : Reg.r7 ∉ linkRegs), h.r3, h.r4, h.r5, h.r6, h.r7, ofNat_toNat' h.hlen,
    ofNat_toNat' hr, ofNat_toNat' (Nat.lt_trans h.hpos hr)] at hpost
  exact hQ s' hrd hwr hsp hcs (by simpa using hf) hpost.1 hpost.2

end

/-! ## `vg_keccak_pad` -/

section
variable {s : State} {st scr : Addr} {rate pos : Nat}

/-- The facts a call of `vg_keccak_pad(st, rate, pos, suffix, scr)` needs. -/
structure PadArgs (s : State) (st scr : Addr) (rate pos : Nat) : Prop where
  r3 : s.gpr .r3 = st
  r4 : s.gpr .r4 = BitVec.ofNat 64 rate
  r5 : s.gpr .r5 = BitVec.ofNat 64 pos
  r7 : s.gpr .r7 = scr
  hrate : rate ∈ rates
  hpos : pos < rate
  sp48 : 48 ≤ s.sp.toNat
  st_scr : Region.Disjoint ⟨st, 200⟩ ⟨scr, 640⟩
  k_st : (below s.sp 48).Disjoint ⟨st, 200⟩
  k_scr : (below s.sp 48).Disjoint ⟨scr, 640⟩

theorem pad_pre (h : PadArgs s st scr rate pos) :
    Proof.Sha3.padPPC64LE.pre (s.callEntry.withRegions [] [⟨st, 200⟩, ⟨scr, 640⟩]) := by
  have hr := rate_lt h.hrate
  simp only [Proof.Sha3.padPPC64LE, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, ce_gpr s _ _ (by decide : Reg.r3 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.r4 ∉ linkRegs),
    ce_gpr s _ _ (by decide : Reg.r5 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.r7 ∉ linkRegs), h.r3, h.r4, h.r5,
    h.r7, ofNat_toNat' hr, ofNat_toNat' (Nat.lt_trans h.hpos hr)]
  exact ⟨trivial, trivial, h.st_scr, h.sp48, h.k_st, h.k_scr, h.hrate, h.hpos⟩

theorem pad_call (h : PadArgs s st scr rate pos)
    (hc : Covers ([] ++ [⟨st, 200⟩, ⟨scr, 640⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨scr, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨scr, 640⟩, below s.sp 48] s.mem s'.mem →
      (∀ msg, Spec.Sha3.Repr s.mem st rate msg → pos = msg.length % rate →
        stateAt s'.mem st = absorb rate (pad rate ((s.gpr .r6).setWidth 8) msg)) → Q s') :
    WP isa (.call "vg_keccak_pad_scratch" Impl.Sha3.PPC64LE.Stream.pad) s Q := by
  have hr := rate_lt h.hrate
  refine call48 (k := Proof.Sha3.padPPC64LE) Proof.Sha3.PPC64LE.Stream.pad_correct Sample.pad_sdepth
    (pad_pre h) hc hw fun s' hrd hwr hsp hf hcs hpost => ?_
  simp only [Proof.Sha3.padPPC64LE, State.withRegions_mem, State.callEntry_mem,
    ce_gpr s _ _ (by decide : Reg.r3 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.r4 ∉ linkRegs),
    ce_gpr s _ _ (by decide : Reg.r5 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.r6 ∉ linkRegs), h.r3, h.r4, h.r5,
    ofNat_toNat' hr, ofNat_toNat' (Nat.lt_trans h.hpos hr)] at hpost
  exact hQ s' hrd hwr hsp hcs (by simpa using hf) hpost

end

/-! ## `vg_keccak_squeeze` -/

section
variable {s : State} {st op scr : Addr} {rate pos len : Nat}

/-- The facts a call of `vg_keccak_squeeze(st, rate, pos, op, len, scr)` needs. -/
structure SqueezeArgs (s : State) (st op scr : Addr) (rate pos len : Nat) : Prop where
  r3 : s.gpr .r3 = st
  r4 : s.gpr .r4 = BitVec.ofNat 64 rate
  r5 : s.gpr .r5 = BitVec.ofNat 64 pos
  r6 : s.gpr .r6 = op
  r7 : s.gpr .r7 = BitVec.ofNat 64 len
  r8 : s.gpr .r8 = scr
  hrate : rate ∈ rates
  hpos : pos ≤ rate
  hlen : len < 2 ^ 64
  sp48 : 48 ≤ s.sp.toNat
  st_o : Region.Disjoint ⟨st, 200⟩ ⟨op, len⟩
  st_scr : Region.Disjoint ⟨st, 200⟩ ⟨scr, 640⟩
  o_scr : Region.Disjoint ⟨op, len⟩ ⟨scr, 640⟩
  k_st : (below s.sp 48).Disjoint ⟨st, 200⟩
  k_o : (below s.sp 48).Disjoint ⟨op, len⟩
  k_scr : (below s.sp 48).Disjoint ⟨scr, 640⟩

theorem squeeze_pre (h : SqueezeArgs s st op scr rate pos len) :
    Proof.Sha3.squeezePPC64LE.pre (s.callEntry.withRegions [] [⟨st, 200⟩, ⟨op, len⟩, ⟨scr, 640⟩]) := by
  have hr := rate_lt h.hrate
  simp only [Proof.Sha3.squeezePPC64LE, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, ce_gpr s _ _ (by decide : Reg.r3 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.r4 ∉ linkRegs),
    ce_gpr s _ _ (by decide : Reg.r5 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.r6 ∉ linkRegs),
    ce_gpr s _ _ (by decide : Reg.r7 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.r8 ∉ linkRegs), h.r3, h.r4, h.r5,
    h.r6, h.r7, h.r8, ofNat_toNat' h.hlen, ofNat_toNat' hr, ofNat_toNat' (Nat.lt_of_le_of_lt h.hpos hr)]
  exact ⟨trivial, trivial, h.st_o, h.st_scr, h.o_scr, h.sp48, h.k_st, h.k_o, h.k_scr, h.hrate, h.hpos⟩

theorem squeeze_call (h : SqueezeArgs s st op scr rate pos len)
    (hc : Covers ([] ++ [⟨st, 200⟩, ⟨op, len⟩, ⟨scr, 640⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨op, len⟩, ⟨scr, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨op, len⟩, ⟨scr, 640⟩, below s.sp 48] s.mem s'.mem →
      bytesAt s'.mem op len = squeezeFrom rate (stateAt s.mem st) pos len →
      (s'.gpr .r3).toNat ≤ rate →
      (∀ d, squeezeFrom rate (stateAt s'.mem st) (s'.gpr .r3).toNat d =
        squeezeFrom rate (stateAt s.mem st) (pos + len) d) → Q s') :
    WP isa (.call "vg_keccak_squeeze_scratch" Impl.Sha3.PPC64LE.Stream.squeeze) s Q := by
  have hr := rate_lt h.hrate
  refine call48 (k := Proof.Sha3.squeezePPC64LE) Proof.Sha3.PPC64LE.Stream.squeeze_correct Sample.squeeze_sdepth
    (squeeze_pre h) hc hw fun s' hrd hwr hsp hf hcs hpost => ?_
  simp only [Proof.Sha3.squeezePPC64LE, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    ce_gpr s _ _ (by decide : Reg.r3 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.r4 ∉ linkRegs),
    ce_gpr s _ _ (by decide : Reg.r5 ∉ linkRegs), ce_gpr s _ _ (by decide : Reg.r6 ∉ linkRegs),
    ce_gpr s _ _ (by decide : Reg.r7 ∉ linkRegs), h.r3, h.r4, h.r5, h.r6, h.r7, ofNat_toNat' h.hlen,
    ofNat_toNat' hr, ofNat_toNat' (Nat.lt_of_le_of_lt h.hpos hr)] at hpost
  exact hQ s' hrd hwr hsp hcs (by simpa using hf) hpost.1 hpost.2.1 hpost.2.2

end

end VG.Proof.MlKem.PPC64LE
