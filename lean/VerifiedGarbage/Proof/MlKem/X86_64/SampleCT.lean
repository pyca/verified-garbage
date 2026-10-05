import VerifiedGarbage.Impl.MlKem.X86_64.Frag
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Squeeze
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Impl.MlKem.X86_64.Sample
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Semantics

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.KCall`. -/
section

/-!
# ML-KEM on x86-64: calling the SHA-3 sponge

Calls of `vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze` from
their proofs (`WP.call`): the callee's precondition on entry (`absorb_pre`,
`pad_pre`, `squeeze_pre`, which the constant-time proofs of callers use too),
and what holds when it returns (`absorb_call`, `pad_call`, `squeeze_call`). A
caller gives each call 16 bytes of stack below `rsp` (the return address and
that of the permutation's call).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64
open VG.Spec.Sha3 (stateAt bytesAt absorb pad rates squeezeFrom)

/-! ## The stack of a call -/

theorem sub_ret (sp : Addr) : Region.Sub ⟨sp - 8, 8⟩ (below sp 16) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (sp - BitVec.ofNat 64 16) = (x - (sp - 8)) + 8 by bv_omega, BitVec.toNat_add]
  have : (8 : BitVec 64).toNat = 8 := rfl
  omega

theorem sub_stk (sp : Addr) : Region.Sub ⟨sp - 8 - 8, 8⟩ (below sp 16) := by
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (sp - BitVec.ofNat 64 16) = x - (sp - 8 - 8) by bv_omega]
  omega

theorem sub_b8 (sp : Addr) : Region.Sub (below sp 8) (below sp 16) := below_sub (by omega) (by omega)

/-- A region apart from the 16 bytes below `rsp` reads the same on entry to a callee. -/
theorem callEntry_bytes (s : State) {R : Region} (hd : (below (s.gpr .rsp) 16).Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    s.callEntry.mem (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (rs := [below (s.gpr .rsp) 8])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega)))
    (by simpa using (hd.sub_left (VG.Proof.MlKem.X86_64.sub_b8 _)).symm) hR hi

theorem callEntry_stateAt (s : State) {p : Addr} (hd : (below (s.gpr .rsp) 16).Disjoint ⟨p, 200⟩) :
    stateAt s.callEntry.mem p = stateAt s.mem p :=
  Proof.Sha3.stateAt_congr fun _ hi => VG.Proof.MlKem.X86_64.callEntry_bytes s (R := ⟨p, 200⟩) hd (by simp) hi

theorem callEntry_bytesAt (s : State) {p : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (hd : (below (s.gpr .rsp) 16).Disjoint ⟨p, n⟩) : bytesAt s.callEntry.mem p n = bytesAt s.mem p n :=
  bytesAt_congr fun _ hi => VG.Proof.MlKem.X86_64.callEntry_bytes s (R := ⟨p, n⟩) hd (by simp; omega) hi

theorem callEntry_repr (s : State) {p : Addr} (hd : (below (s.gpr .rsp) 16).Disjoint ⟨p, 200⟩)
    {rate : Nat} {msg : List Byte} : Spec.Sha3.Repr s.callEntry.mem p rate msg ↔ Spec.Sha3.Repr s.mem p rate msg := by
  unfold Spec.Sha3.Repr; rw [VG.Proof.MlKem.X86_64.callEntry_stateAt s hd]

theorem ce_gpr (s : State) {r : Reg} (h : r ≠ .rsp) : s.callEntry.gpr r = s.gpr r := State.callEntry_gpr _ h

/-! ## The callees' registers and stack -/

theorem absorb_nosp : NoSp Impl.Sha3.X86_64.Stream.absorb := by
  have : ((instrs Impl.Sha3.X86_64.Stream.absorb).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem pad_nosp : NoSp Impl.Sha3.X86_64.Stream.pad := by
  have : ((instrs Impl.Sha3.X86_64.Stream.pad).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem squeeze_nosp : NoSp Impl.Sha3.X86_64.Stream.squeeze := by
  have : ((instrs Impl.Sha3.X86_64.Stream.squeeze).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem absorb_depth : Impl.Sha3.X86_64.Stream.absorb.depth = 1 := by decide +kernel
theorem pad_depth : Impl.Sha3.X86_64.Stream.pad.depth = 1 := by decide +kernel
theorem squeeze_depth : Impl.Sha3.X86_64.Stream.squeeze.depth = 1 := by decide +kernel

/-! ## `vg_keccak_absorb` -/

section
variable {s : State} {st dp scr : Addr} {rate pos len : Nat}

/-- The facts a call of `vg_keccak_absorb(st, rate, pos, dp, len, scr)` needs. -/
structure AbsorbArgs (s : State) (st dp scr : Addr) (rate pos len : Nat) : Prop where
  rdi : s.gpr .rdi = st
  rsi : s.gpr .rsi = BitVec.ofNat 64 rate
  rdx : s.gpr .rdx = BitVec.ofNat 64 pos
  rcx : s.gpr .rcx = dp
  r8 : s.gpr .r8 = BitVec.ofNat 64 len
  r9 : s.gpr .r9 = scr
  hrate : rate ∈ rates
  hpos : pos < rate
  hlen : len < 2 ^ 64
  st_scr : Region.Disjoint ⟨st, 200⟩ ⟨scr, 640⟩
  d_st : Region.Disjoint ⟨dp, len⟩ ⟨st, 200⟩
  d_scr : Region.Disjoint ⟨dp, len⟩ ⟨scr, 640⟩
  k_st : (below (s.gpr .rsp) 16).Disjoint ⟨st, 200⟩
  k_d : (below (s.gpr .rsp) 16).Disjoint ⟨dp, len⟩
  k_scr : (below (s.gpr .rsp) 16).Disjoint ⟨scr, 640⟩

theorem rate_lt {rate : Nat} (h : rate ∈ rates) : rate < 2 ^ 64 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem ofNat_toNat' {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem absorb_pre (h : VG.Proof.MlKem.X86_64.AbsorbArgs s st dp scr rate pos len) :
    Proof.Sha3.absorbX86_64.pre (s.callEntry.withRegions [⟨dp, len⟩] [⟨st, 200⟩, ⟨scr, 640⟩]) := by
  have hr := VG.Proof.MlKem.X86_64.rate_lt h.hrate
  simp only [Proof.Sha3.absorbX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rdi ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rsi ≠ .rsp),
    VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rdx ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rcx ≠ .rsp),
    VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.r8 ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx,
    h.r8, h.r9, VG.Proof.MlKem.X86_64.ofNat_toNat' h.hlen, VG.Proof.MlKem.X86_64.ofNat_toNat' hr, VG.Proof.MlKem.X86_64.ofNat_toNat' (Nat.lt_trans h.hpos hr)]
  exact ⟨trivial, trivial, h.st_scr, h.d_st, h.d_scr, h.k_st.sub_left (VG.Proof.MlKem.X86_64.sub_ret _), h.k_scr.sub_left (VG.Proof.MlKem.X86_64.sub_ret _),
    h.k_st.sub_left (VG.Proof.MlKem.X86_64.sub_stk _), h.k_d.sub_left (VG.Proof.MlKem.X86_64.sub_stk _), h.k_scr.sub_left (VG.Proof.MlKem.X86_64.sub_stk _), h.hrate, h.hpos⟩

theorem absorb_call (h : VG.Proof.MlKem.X86_64.AbsorbArgs s st dp scr rate pos len)
    (hc : Covers ([⟨dp, len⟩] ++ [⟨st, 200⟩, ⟨scr, 640⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨scr, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨scr, 640⟩, below (s.gpr .rsp) 16] s.mem s'.mem →
      (∀ msg, Spec.Sha3.Repr s.mem st rate msg → pos = msg.length % rate →
        Spec.Sha3.Repr s'.mem st rate (msg ++ bytesAt s.mem dp len)) →
      (s'.gpr .rax).toNat = (pos + len) % rate → Q s') :
    WP isa (.call "vg_keccak_absorb_scratch" Impl.Sha3.X86_64.Stream.absorb) s Q := by
  have hr := VG.Proof.MlKem.X86_64.rate_lt h.hrate
  refine WP.call (k := Proof.Sha3.absorbX86_64) Proof.Sha3.X86_64.Stream.Absorb.absorb_correct VG.Proof.MlKem.X86_64.absorb_nosp
    (by rw [VG.Proof.MlKem.X86_64.absorb_depth]; decide) (VG.Proof.MlKem.X86_64.absorb_pre h) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost, hrax⟩
  simp only [State.withRegions_gpr, State.withRegions_mem, VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rsi ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rcx ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx,
    h.r8, hm₂, VG.Proof.MlKem.X86_64.ofNat_toNat' h.hlen, VG.Proof.MlKem.X86_64.ofNat_toNat' hr, VG.Proof.MlKem.X86_64.ofNat_toNat' (Nat.lt_trans h.hpos hr)] at hpost hrax
  refine hQ s' hrd hwr hcs (by rw [VG.Proof.MlKem.X86_64.absorb_depth] at hf; simpa using hf) (fun msg hm hp => ?_)
    (by rw [← hg₂ _ (by decide)]; exact hrax)
  have := hpost msg ((VG.Proof.MlKem.X86_64.callEntry_repr s h.k_st).mpr hm) hp
  rwa [VG.Proof.MlKem.X86_64.callEntry_bytesAt s h.hlen h.k_d] at this

end

/-! ## `vg_keccak_pad` -/

section
variable {s : State} {st scr : Addr} {rate pos : Nat} {suffix : BitVec 64}

/-- The facts a call of `vg_keccak_pad(st, rate, pos, suffix, scr)` needs. -/
structure PadArgs (s : State) (st scr : Addr) (rate pos : Nat) : Prop where
  rdi : s.gpr .rdi = st
  rsi : s.gpr .rsi = BitVec.ofNat 64 rate
  rdx : s.gpr .rdx = BitVec.ofNat 64 pos
  r8 : s.gpr .r8 = scr
  hrate : rate ∈ rates
  hpos : pos < rate
  st_scr : Region.Disjoint ⟨st, 200⟩ ⟨scr, 640⟩
  k_st : (below (s.gpr .rsp) 16).Disjoint ⟨st, 200⟩
  k_scr : (below (s.gpr .rsp) 16).Disjoint ⟨scr, 640⟩

theorem pad_pre (h : VG.Proof.MlKem.X86_64.PadArgs s st scr rate pos) :
    Proof.Sha3.padX86_64.pre (s.callEntry.withRegions [] [⟨st, 200⟩, ⟨scr, 640⟩]) := by
  have hr := VG.Proof.MlKem.X86_64.rate_lt h.hrate
  simp only [Proof.Sha3.padX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rdi ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rsi ≠ .rsp),
    VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rdx ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.r8,
    VG.Proof.MlKem.X86_64.ofNat_toNat' hr, VG.Proof.MlKem.X86_64.ofNat_toNat' (Nat.lt_trans h.hpos hr)]
  exact ⟨trivial, trivial, h.st_scr, h.k_st.sub_left (VG.Proof.MlKem.X86_64.sub_ret _), h.k_scr.sub_left (VG.Proof.MlKem.X86_64.sub_ret _),
    h.k_st.sub_left (VG.Proof.MlKem.X86_64.sub_stk _), h.k_scr.sub_left (VG.Proof.MlKem.X86_64.sub_stk _), h.hrate, h.hpos⟩

theorem pad_call (h : VG.Proof.MlKem.X86_64.PadArgs s st scr rate pos)
    (hc : Covers ([] ++ [⟨st, 200⟩, ⟨scr, 640⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨scr, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨scr, 640⟩, below (s.gpr .rsp) 16] s.mem s'.mem →
      (∀ msg, Spec.Sha3.Repr s.mem st rate msg → pos = msg.length % rate →
        stateAt s'.mem st = absorb rate (pad rate ((s.gpr .rcx).setWidth 8) msg)) → Q s') :
    WP isa (.call "vg_keccak_pad_scratch" Impl.Sha3.X86_64.Stream.pad) s Q := by
  have hr := VG.Proof.MlKem.X86_64.rate_lt h.hrate
  refine WP.call (k := Proof.Sha3.padX86_64) Proof.Sha3.X86_64.Stream.Pad.pad_correct VG.Proof.MlKem.X86_64.pad_nosp
    (by rw [VG.Proof.MlKem.X86_64.pad_depth]; decide) (VG.Proof.MlKem.X86_64.pad_pre h) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost⟩
  simp only [Proof.Sha3.padX86_64, State.withRegions_gpr, State.withRegions_mem, VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rsi ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rcx ≠ .rsp), h.rdi, h.rsi, h.rdx, hm₂, VG.Proof.MlKem.X86_64.ofNat_toNat' hr,
    VG.Proof.MlKem.X86_64.ofNat_toNat' (Nat.lt_trans h.hpos hr)] at hpost
  exact hQ s' hrd hwr hcs (by rw [VG.Proof.MlKem.X86_64.pad_depth] at hf; simpa using hf)
    (fun msg hm hp => hpost msg ((VG.Proof.MlKem.X86_64.callEntry_repr s h.k_st).mpr hm) hp)

end

/-! ## `vg_keccak_squeeze` -/

section
variable {s : State} {st out scr : Addr} {rate pos len : Nat}

/-- The facts a call of `vg_keccak_squeeze(st, rate, pos, out, len, scr)` needs. -/
structure SqueezeArgs (s : State) (st out scr : Addr) (rate pos len : Nat) : Prop where
  rdi : s.gpr .rdi = st
  rsi : s.gpr .rsi = BitVec.ofNat 64 rate
  rdx : s.gpr .rdx = BitVec.ofNat 64 pos
  rcx : s.gpr .rcx = out
  r8 : s.gpr .r8 = BitVec.ofNat 64 len
  r9 : s.gpr .r9 = scr
  hrate : rate ∈ rates
  hpos : pos ≤ rate
  hlen : len < 2 ^ 64
  st_out : Region.Disjoint ⟨st, 200⟩ ⟨out, len⟩
  st_scr : Region.Disjoint ⟨st, 200⟩ ⟨scr, 640⟩
  out_scr : Region.Disjoint ⟨out, len⟩ ⟨scr, 640⟩
  k_st : (below (s.gpr .rsp) 16).Disjoint ⟨st, 200⟩
  k_out : (below (s.gpr .rsp) 16).Disjoint ⟨out, len⟩
  k_scr : (below (s.gpr .rsp) 16).Disjoint ⟨scr, 640⟩

theorem squeeze_pre (h : VG.Proof.MlKem.X86_64.SqueezeArgs s st out scr rate pos len) :
    Proof.Sha3.squeezeX86_64.pre (s.callEntry.withRegions [] [⟨st, 200⟩, ⟨out, len⟩, ⟨scr, 640⟩]) := by
  have hr := VG.Proof.MlKem.X86_64.rate_lt h.hrate
  simp only [Proof.Sha3.squeezeX86_64, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.callEntry_rsp, VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rdi ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rsi ≠ .rsp),
    VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rdx ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rcx ≠ .rsp),
    VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.r8 ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.r9 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx,
    h.r8, h.r9, VG.Proof.MlKem.X86_64.ofNat_toNat' h.hlen, VG.Proof.MlKem.X86_64.ofNat_toNat' hr, VG.Proof.MlKem.X86_64.ofNat_toNat' (Nat.lt_of_le_of_lt h.hpos hr)]
  exact ⟨trivial, trivial, h.st_out, h.st_scr, h.out_scr, h.k_st.sub_left (VG.Proof.MlKem.X86_64.sub_ret _), h.k_out.sub_left (VG.Proof.MlKem.X86_64.sub_ret _),
    h.k_scr.sub_left (VG.Proof.MlKem.X86_64.sub_ret _), h.k_st.sub_left (VG.Proof.MlKem.X86_64.sub_stk _), h.k_out.sub_left (VG.Proof.MlKem.X86_64.sub_stk _),
    h.k_scr.sub_left (VG.Proof.MlKem.X86_64.sub_stk _), h.hrate, h.hpos⟩

theorem squeeze_call (h : VG.Proof.MlKem.X86_64.SqueezeArgs s st out scr rate pos len)
    (hc : Covers ([] ++ [⟨st, 200⟩, ⟨out, len⟩, ⟨scr, 640⟩]) (s.rd ++ s.wr))
    (hw : Covers [⟨st, 200⟩, ⟨out, len⟩, ⟨scr, 640⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨out, len⟩, ⟨scr, 640⟩, below (s.gpr .rsp) 16] s.mem s'.mem →
      bytesAt s'.mem out len = squeezeFrom rate (stateAt s.mem st) pos len → Q s') :
    WP isa (.call "vg_keccak_squeeze_scratch" Impl.Sha3.X86_64.Stream.squeeze) s Q := by
  have hr := VG.Proof.MlKem.X86_64.rate_lt h.hrate
  refine WP.call (k := Proof.Sha3.squeezeX86_64) Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct VG.Proof.MlKem.X86_64.squeeze_nosp
    (by rw [VG.Proof.MlKem.X86_64.squeeze_depth]; decide) (VG.Proof.MlKem.X86_64.squeeze_pre h) hc hw ?_
  intro s' hrd hwr hcs hf _ ⟨s₂, hm₂, hg₂, hpost, _⟩
  simp only [State.withRegions_gpr, State.withRegions_mem, VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rdi ≠ .rsp),
    VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rsi ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rdx ≠ .rsp),
    VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.rcx ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr s (by decide : Reg.r8 ≠ .rsp), h.rdi, h.rsi, h.rdx, h.rcx,
    h.r8, hm₂, VG.Proof.MlKem.X86_64.ofNat_toNat' h.hlen, VG.Proof.MlKem.X86_64.ofNat_toNat' hr, VG.Proof.MlKem.X86_64.ofNat_toNat' (Nat.lt_of_le_of_lt h.hpos hr)] at hpost
  refine hQ s' hrd hwr hcs (by rw [VG.Proof.MlKem.X86_64.squeeze_depth] at hf; simpa using hf) ?_
  rw [hpost, VG.Proof.MlKem.X86_64.callEntry_stateAt s h.k_st]

end

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.SampleLoop`. -/
section

/-!
# ML-KEM on x86-64: the loop of `vg_mlkem_sample_ntt`

An iteration of the loop does what `sampleStepCap` does to the coefficients
sampled so far, stored at `a` (`Stored`) and counted in `rdi` (`snBody_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## The values of an iteration -/

/-- `d₁` of the bytes `c₀`, `c₁`, as the code computes it. -/
def d1w (c0 c1 : Byte) : BitVec 32 :=
  (BitVec.setWidth 32 (BitVec.setWidth 64 c1) &&& 15).rotateRight 24 + BitVec.setWidth 32 (BitVec.setWidth 64 c0)

/-- `d₂` of the bytes `c₁`, `c₂`, as the code computes it. -/
def d2w (c1 c2 : Byte) : BitVec 32 :=
  (BitVec.setWidth 32 (BitVec.setWidth 64 c2)).rotateRight 28 + BitVec.setWidth 32 (BitVec.setWidth 64 c1) >>> 4

theorem b32 (c : Byte) : (BitVec.setWidth 32 (BitVec.setWidth 64 c)).toNat = c.toNat := by
  rw [BitVec.toNat_setWidth, toNat_setWidth64_8, Nat.mod_eq_of_lt (by have := c.isLt; omega)]

theorem d1w_toNat (c0 c1 : Byte) : (VG.Proof.MlKem.X86_64.d1w c0 c1).toNat = c0.toNat + 256 * (c1.toNat % 16) := by
  have h0 := c0.isLt
  have e : (BitVec.setWidth 32 (BitVec.setWidth 64 c1) &&& 15).toNat = c1.toNat % 16 := by
    rw [BitVec.toNat_and, VG.Proof.MlKem.X86_64.b32, show (15 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hr := rotr_toNat (BitVec.setWidth 32 (BitVec.setWidth 64 c1) &&& 15) (r := 24) (by decide)
    (by rw [e]; have := Nat.mod_lt c1.toNat (show 16 > 0 by decide); omega)
  rw [e] at hr
  have := Nat.mod_lt c1.toNat (show 16 > 0 by decide)
  rw [VG.Proof.MlKem.X86_64.d1w, BitVec.toNat_add, hr, VG.Proof.MlKem.X86_64.b32]
  rw [show 32 - 24 = 8 from rfl]; omega

theorem d2w_toNat (c1 c2 : Byte) : (VG.Proof.MlKem.X86_64.d2w c1 c2).toNat = c1.toNat / 16 + 16 * c2.toNat := by
  have h1 := c1.isLt
  have h2 := c2.isLt
  have hr := rotr_toNat (BitVec.setWidth 32 (BitVec.setWidth 64 c2)) (r := 28) (by decide)
    (by rw [VG.Proof.MlKem.X86_64.b32]; omega)
  rw [VG.Proof.MlKem.X86_64.b32] at hr
  rw [VG.Proof.MlKem.X86_64.d2w, BitVec.toNat_add, hr, shr_toNat, VG.Proof.MlKem.X86_64.b32]
  rw [show 32 - 28 = 4 from rfl]; omega

theorem sx256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide

theorem snLoad_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 1) 1)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 2) 1) :
    WP isa (.block snLoad) s fun s' =>
      (s'.gpr .r9 = BitVec.setWidth 64 (VG.Proof.MlKem.X86_64.d1w (s.mem (s.gpr .rsi)) (s.mem (s.gpr .rsi + BitVec.ofNat 64 1))) ∧
        s'.gpr .r8 = BitVec.setWidth 64 (VG.Proof.MlKem.X86_64.d2w (s.mem (s.gpr .rsi + BitVec.ofNat 64 1))
          (s.mem (s.gpr .rsi + BitVec.ofNat 64 2))) ∧
        s'.cf = some (decide ((s.gpr .rdi).toNat < 256)) ∧ s'.mem = s.mem ∧ s'.gpr .rdi = s.gpr .rdi) ∧
      Keep [.rax, .rdx, .r8, .r9, .rdi] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold snLoad
  xrun [h0, h1, h2, VG.Proof.MlKem.X86_64.sx256, VG.Proof.MlKem.X86_64.d1w, VG.Proof.MlKem.X86_64.d2w, show (256 : BitVec 64).toNat = 256 from rfl]

/-! ## Storing a coefficient -/

/-- The coefficients `L` are stored at `aP`. -/
def Stored (m : Mem) (aP : Addr) (L : List Zq) : Prop :=
  ∀ k < L.length, coeffAt m aP k = BitVec.ofNat 32 (L.getD k 0).val

theorem ea_aJ (s : State) {aP : Addr} {j : Nat} (hbp : s.gpr .rbp = aP) (hdi : s.gpr .rdi = BitVec.ofNat 64 j)
    (_hj : j < 256) : s.ea aJ = coeffAddr aP j := by
  simp only [State.ea, aJ, hbp, hdi]
  rw [coeffAddr, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem stored_snoc {m : Mem} {aP : Addr} {L : List Zq} (h : VG.Proof.MlKem.X86_64.Stored m aP L) (hL : L.length < 256) {v : BitVec 32}
    (hv : v.toNat < q) : VG.Proof.MlKem.X86_64.Stored (m.writeW (coeffAddr aP L.length) v) aP (L ++ [ofNat v.toNat]) := by
  intro k hk
  rw [List.length_append, List.length_singleton] at hk
  rw [coeffAt_writeW _ _ (show k < 256 by omega) hL]
  by_cases e : L.length = k
  · subst e
    rw [ifp rfl, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    simp only [List.getElem?_cons_zero, Option.getD_some]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ofNat_of_lt hv, Nat.mod_eq_of_lt (by rw [q_eq] at hv; omega)]
  · rw [ifn e, h k (by omega), List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]

theorem ofNat64_succ {j : Nat} (_h : j + 1 < 2 ^ 64) : BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem sxZero : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide

/-- A write past the coefficients keeps them. -/
theorem stored_write {m : Mem} {aP : Addr} {L : List Zq} (h : VG.Proof.MlKem.X86_64.Stored m aP L) (hL : L.length < 256) (v : BitVec 32) :
    VG.Proof.MlKem.X86_64.Stored (m.writeW (coeffAddr aP L.length) v) aP L := by
  intro k hk
  rw [coeffAt_writeW _ _ (show k < 256 by omega) hL, ifn (by omega)]
  exact h k hk

/-- The coefficients at `aP` may be written. -/
def WrA (wr : List Region) (aP : Addr) : Prop := ∀ j < 256, InRegions wr (coeffAddr aP j) 4

theorem WrA.of_mem {wr : List Region} {aP : Addr} (h : pR aP ∈ wr) : VG.Proof.MlKem.X86_64.WrA wr aP := fun _ hj =>
  ⟨_, h, coeff_contains _ hj⟩

/-- Store the value of `r` to `a[j]`, and count it if it is less than `q`. -/
theorem snTry_ok (r : Reg) (s : State) {aP : Addr} {L : List Zq} (hbp : s.gpr .rbp = aP)
    (hdi : s.gpr .rdi = BitVec.ofNat 64 L.length) (hL : L.length < 256) (hw : VG.Proof.MlKem.X86_64.WrA s.wr aP)
    (hst : VG.Proof.MlKem.X86_64.Stored s.mem aP L) :
    WP isa (.block (snTry r)) s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (if ((s.gpr r).setWidth 32).toNat < q
        then L ++ [ofNat ((s.gpr r).setWidth 32).toNat] else L).length ∧
      VG.Proof.MlKem.X86_64.Stored s'.mem aP (if ((s.gpr r).setWidth 32).toNat < q
        then L ++ [ofNat ((s.gpr r).setWidth 32).toNat] else L) ∧
      Frame [pR aP] s.mem s'.mem ∧ Keep [.rdi, r] s s' := by
  have ha := VG.Proof.MlKem.X86_64.ea_aJ s hbp hdi hL
  have hin : InRegions s.wr (coeffAddr aP L.length) 4 := hw _ hL
  refine WP.mono (WP.keep [.rdi, r] (Q := fun s' =>
      s'.mem = s.mem.writeW (coeffAddr aP L.length) ((s.gpr r).setWidth 32) ∧
      s'.gpr .rdi = s.gpr .rdi + BitVec.setWidth 64 (BitVec.ofBool (decide (((s.gpr r).setWidth 32).toNat < 3329))))
    (by unfold snTry; xrun [ha, hin, qImm_toNat, VG.Proof.MlKem.X86_64.sxZero]; exact congrArg (· + _) (BitVec.add_zero _))
    (by cases r <;> decide))
    fun s' ⟨⟨hm, hdi'⟩, k⟩ => ?_
  have hf : Frame [pR aP] s.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hL)
  by_cases hb : ((s.gpr r).setWidth 32).toNat < q
  · have hb' : ((s.gpr r).setWidth 32).toNat < 3329 := by rw [q_eq] at hb; exact hb
    rw [ifp hb]
    refine ⟨?_, by rw [hm]; exact VG.Proof.MlKem.X86_64.stored_snoc hst hL hb, hf, k⟩
    rw [hdi', hdi, decide_eq_true hb', List.length_append, List.length_singleton]
    exact VG.Proof.MlKem.X86_64.ofNat64_succ (by omega)
  · have hb' : ¬ ((s.gpr r).setWidth 32).toNat < 3329 := by rw [q_eq] at hb; exact hb
    rw [ifn hb]
    refine ⟨?_, by rw [hm]; exact VG.Proof.MlKem.X86_64.stored_write hst hL _, hf, k⟩
    rw [hdi', hdi, decide_eq_false hb']
    exact BitVec.add_zero _

/-! ## An iteration -/

/-- Lines 5–15 of Algorithm 7 on the values `d₁`, `d₂`. -/
def stepD (L : List Zq) (d1 d2 : Nat) : List Zq :=
  let a := if d1 < q then L ++ [ofNat d1] else L
  if d2 < q ∧ a.length < n then a ++ [ofNat d2] else a

theorem sampleStep_eq (L : List Zq) (c0 c1 c2 : Byte) :
    sampleStep L c0 c1 c2 = VG.Proof.MlKem.X86_64.stepD L (c0.toNat + 256 * (c1.toNat % 16)) (c1.toNat / 16 + 16 * c2.toNat) := rfl

theorem cmpRdi_ok (s : State) :
    WP isa (.block [.alu .cmp .rdi (.imm 256)]) s fun s' =>
      s'.cf = some (decide ((s.gpr .rdi).toNat < 256)) ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr := by
  xrun [VG.Proof.MlKem.X86_64.sx256, show (256 : BitVec 64).toNat = 256 from rfl]

theorem ofNat64_toNat {j : Nat} (h : j < 2 ^ 64) : (BitVec.ofNat 64 j).toNat = j := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The coefficients after an iteration, from `L` and the values `d₁`, `d₂`. -/
def midL (L : List Zq) (d1 d2 : Nat) : List Zq := if L.length < 256 then VG.Proof.MlKem.X86_64.stepD L d1 d2 else L

/-- The two tries, if `j < 256`. -/
theorem snMid_ok (s : State) {aP : Addr} {L : List Zq} (hbp : s.gpr .rbp = aP)
    (hdi : s.gpr .rdi = BitVec.ofNat 64 L.length) (hL : L.length ≤ 256) (hw : VG.Proof.MlKem.X86_64.WrA s.wr aP)
    (hst : VG.Proof.MlKem.X86_64.Stored s.mem aP L) (hcf : s.cf = some (decide ((s.gpr .rdi).toNat < 256))) :
    WP isa (.ite .b (.seq (.block (snTry .r9)) (.seq (.block [.alu .cmp .rdi (.imm 256)]) (.ite .b (.block (snTry .r8)) (.block []))))
        (.block [])) s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlKem.X86_64.midL L ((s.gpr .r9).setWidth 32).toNat ((s.gpr .r8).setWidth 32).toNat).length ∧
        VG.Proof.MlKem.X86_64.Stored s'.mem aP (VG.Proof.MlKem.X86_64.midL L ((s.gpr .r9).setWidth 32).toNat ((s.gpr .r8).setWidth 32).toNat) ∧
        Frame [pR aP] s.mem s'.mem ∧ Keep [.rdi, .r9, .r8] s s' := by
  have hl : (s.gpr .rdi).toNat = L.length := by rw [hdi, VG.Proof.MlKem.X86_64.ofNat64_toNat (by omega)]
  refine WP.ite (decide (L.length < 256)) (by rw [← hl]; exact hcf) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    rw [VG.Proof.MlKem.X86_64.midL, ifp hb]
    refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.snTry_ok .r9 s hbp hdi hb hw hst) fun s2 ⟨hdi2, hst2, hf2, k2⟩ => ?_)
    refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.cmpRdi_ok s2) fun s3 ⟨hc3, hm3, hg3, hrd3, hwr3⟩ => ?_)
    have h8 : s3.gpr .r8 = s.gpr .r8 := by rw [hg3, k2.gpr (by decide)]
    generalize hL1 : (if ((s.gpr .r9).setWidth 32).toNat < q then
      L ++ [ofNat ((s.gpr .r9).setWidth 32).toNat] else L) = L1 at hdi2 hst2
    have hL1len : L1.length ≤ 256 := by
      rw [← hL1]; split <;> (try simp only [List.length_append, List.length_singleton]) <;> omega
    have hl1 : (s3.gpr .rdi).toNat = L1.length := by rw [hg3, hdi2, VG.Proof.MlKem.X86_64.ofNat64_toNat (by omega)]
    have hstep : VG.Proof.MlKem.X86_64.stepD L ((s.gpr .r9).setWidth 32).toNat ((s.gpr .r8).setWidth 32).toNat =
        if L1.length < 256 then (if ((s.gpr .r8).setWidth 32).toNat < q then
          L1 ++ [ofNat ((s.gpr .r8).setWidth 32).toNat] else L1) else L1 := by
      simp only [VG.Proof.MlKem.X86_64.stepD, hL1, n_eq]
      by_cases h1 : L1.length < 256
      · simp only [h1, ite_true, and_true]
      · simp only [h1, ite_false, and_false]
    rw [hstep]
    refine WP.ite (decide (L1.length < 256)) (by rw [← hl1]; show s3.cf = _; rw [hc3, hg3]) (fun hb' => ?_)
      (fun hb' => ?_)
    · simp only [decide_eq_true_eq] at hb'
      simp only [hb', ite_true]
      refine WP.mono (VG.Proof.MlKem.X86_64.snTry_ok .r8 s3 (aP := aP) (by rw [hg3, k2.gpr (by decide), hbp]) (by rw [hg3, hdi2]) hb'
        (by rw [hwr3, k2.2.2]; exact hw) (by rw [hm3]; exact hst2)) fun s4 ⟨hdi4, hst4, hf4, k4⟩ => ?_
      rw [h8] at hdi4 hst4
      exact ⟨hdi4, hst4, hf2.trans (by rw [← hm3]; exact hf4),
        (k2.trans (⟨fun r _ => by rw [hg3], hrd3, hwr3⟩ : Keep [] s2 s3) |>.trans k4).mono (by simp)⟩
    · simp only [decide_eq_false_iff_not] at hb'
      simp only [hb', ite_false]
      refine WP.block_nil ⟨by rw [hg3, hdi2], by rw [hm3]; exact hst2, by rw [hm3]; exact hf2,
        (k2.trans (⟨fun r _ => by rw [hg3], hrd3, hwr3⟩ : Keep [] s2 s3)).mono (by simp)⟩
  · simp only [decide_eq_false_iff_not] at hb
    rw [VG.Proof.MlKem.X86_64.midL, ifn hb]
    exact WP.block_nil ⟨hdi, hst, Frame.refl _ _, Keep.refl _ _⟩


theorem sw32_64 (x : BitVec 32) : (BitVec.setWidth 64 x).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, toNat_setWidth64, Nat.mod_eq_of_lt x.isLt]

theorem snStep_ok (s : State) :
    WP isa (.block [.alu .add .rsi (.imm 3), .alu .sub .rcx (.imm 1)]) s fun s' =>
      (s'.gpr .rsi = s.gpr .rsi + 3 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧
        s'.mem = s.mem) ∧ Keep [.rsi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

/-- An iteration: what `sampleStepCap` does to the coefficients `L`. -/
theorem snBody_ok (s : State) {aP : Addr} {L : List Zq} (hbp : s.gpr .rbp = aP)
    (hdi : s.gpr .rdi = BitVec.ofNat 64 L.length) (hL : L.length ≤ 256) (hw : VG.Proof.MlKem.X86_64.WrA s.wr aP)
    (hst : VG.Proof.MlKem.X86_64.Stored s.mem aP L) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 1) 1)
    (h2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 2) 1) :
    WP isa snBody s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (sampleStepCap L (s.mem (s.gpr .rsi)) (s.mem (s.gpr .rsi + BitVec.ofNat 64 1))
        (s.mem (s.gpr .rsi + BitVec.ofNat 64 2))).length ∧
      VG.Proof.MlKem.X86_64.Stored s'.mem aP (sampleStepCap L (s.mem (s.gpr .rsi)) (s.mem (s.gpr .rsi + BitVec.ofNat 64 1))
        (s.mem (s.gpr .rsi + BitVec.ofNat 64 2))) ∧
      Frame [pR aP] s.mem s'.mem ∧ s'.gpr .rsi = s.gpr .rsi + 3 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ Keep [.rax, .rdx, .r8, .r9, .rdi, .rdi, .rsi, .rcx] s s' := by
  have he : sampleStepCap L (s.mem (s.gpr .rsi)) (s.mem (s.gpr .rsi + BitVec.ofNat 64 1))
        (s.mem (s.gpr .rsi + BitVec.ofNat 64 2)) =
      VG.Proof.MlKem.X86_64.midL L (VG.Proof.MlKem.X86_64.d1w (s.mem (s.gpr .rsi)) (s.mem (s.gpr .rsi + BitVec.ofNat 64 1))).toNat
        (VG.Proof.MlKem.X86_64.d2w (s.mem (s.gpr .rsi + BitVec.ofNat 64 1)) (s.mem (s.gpr .rsi + BitVec.ofNat 64 2))).toNat := by
    rw [sampleStepCap, VG.Proof.MlKem.X86_64.midL, VG.Proof.MlKem.X86_64.sampleStep_eq, VG.Proof.MlKem.X86_64.d1w_toNat, VG.Proof.MlKem.X86_64.d2w_toNat]
    by_cases h : L.length < 256
    · rw [ifn (show ¬ L.length = n by rw [n_eq]; omega), ifp h]
    · rw [ifp (show L.length = n by rw [n_eq]; omega), ifn h]
  rw [he]
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.snLoad_ok s h0 h1 h2) fun s1 ⟨⟨h9, h8, hcf, hm1, hdi1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.snMid_ok s1 (aP := aP) (L := L) (by rw [k1.gpr (by decide), hbp]) (by rw [hdi1, hdi]) hL
    (by rw [k1.2.2]; exact hw) (by rw [hm1]; exact hst) (by rw [hcf, hdi1])) fun s3 ⟨hdi3, hst3, hf3, k3⟩ => ?_)
  rw [h9, h8, VG.Proof.MlKem.X86_64.sw32_64, VG.Proof.MlKem.X86_64.sw32_64] at hdi3 hst3
  refine WP.mono (VG.Proof.MlKem.X86_64.snStep_ok s3) fun s4 ⟨⟨hsi4, hcx4, hz4, hm4⟩, k4⟩ => ?_
  have hsi3 : s3.gpr .rsi = s.gpr .rsi := by rw [k3.gpr (by decide), k1.gpr (by decide)]
  have hcx3 : s3.gpr .rcx = s.gpr .rcx := by rw [k3.gpr (by decide), k1.gpr (by decide)]
  exact ⟨by rw [k4.gpr (by decide), hdi3], by rw [hm4]; exact hst3, by rw [hm4, ← hm1]; exact hf3,
    by rw [hsi4, hsi3], by rw [hcx4, hcx3], by rw [hz4, hcx3], ((k1.trans k3).trans k4).mono (by simp)⟩

theorem off_add (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.FragBase`. -/
section

/-!
# ML-KEM-768 on x86-64: moves, byte stores and copies

The address of a pointer (`pa`), and what `setB` and `copy` do.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.Sha3 (bytesAt)

/-- The address of the pointer `p` in `s`. -/
abbrev pa (s : State) (p : Ptr) : Addr := s.gpr p.1 + BitVec.ofNat 64 p.2

theorem sw_ofNat {n : Nat} (h : n < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_setWidth64, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

/-- A byte of a range. -/
theorem inRegions_byte {rs : List Region} {a : Addr} {n k : Nat} (h : InRegions rs a n) (hk : k < n)
    (hn : n < 2 ^ 64) : InRegions rs (a + BitVec.ofNat 64 k) 1 := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat a (by omega)]; exact hk)⟩

/-! ## A byte -/

theorem b8_ofNat {v : Nat} (_hv : v < 256) :
    BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.ofNat 32 v)) = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem setB_ok (p : Ptr) (v : Nat) (hr : p.1 ≠ .rax) (hv : v < 256) (s : State)
    (hw : InRegions s.wr (VG.Proof.MlKem.X86_64.pa s p) 1) :
    WP isa (.block (setB p v)) s fun s' =>
      s'.mem = s.mem.writeW (VG.Proof.MlKem.X86_64.pa s p) (BitVec.ofNat 8 v) ∧ Keep [.rax] s s' := by
  refine WP.mono (WP.keep [.rax] (Q := fun s' => s'.mem = s.mem.writeW (VG.Proof.MlKem.X86_64.pa s p) (BitVec.ofNat 8 v)) ?_ (by rfl))
    fun s' ⟨h, k⟩ => ⟨h, k⟩
  unfold setB
  xrun [hw, hr, VG.Proof.MlKem.X86_64.b8_ofNat hv]


/-! ## A copy -/

theorem b8b (x : Byte) : BitVec.setWidth 8 (BitVec.setWidth 64 x) = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := x.isLt
  omega

theorem copyBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1) (h1 : InRegions s.wr (s.gpr .rdi) 1) :
    WP isa (.block [.movzx8 .rax (at_ .rsi 0), .store8 (at_ .rdi 0) .rax, .alu .add .rdi (.imm 1),
      .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi) (s.mem (s.gpr .rsi)) ∧ s'.gpr .rdi = s.gpr .rdi + 1 ∧
        s'.gpr .rsi = s.gpr .rsi + 1 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .rdi, .rsi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [h0, h1, VG.Proof.MlKem.X86_64.b8b]

theorem copy_ok (dst src : Ptr) (n : Nat) (hn0 : 0 < n) (hn : n < 2 ^ 31) (hd : dst.2 < 2 ^ 31)
    (hs : src.2 < 2 ^ 31) (hsr : src.1 ≠ .rdi) (s : State)
    (hrd : InRegions (s.rd ++ s.wr) (VG.Proof.MlKem.X86_64.pa s src) n) (hwr : InRegions s.wr (VG.Proof.MlKem.X86_64.pa s dst) n)
    (hdj : Region.Disjoint ⟨VG.Proof.MlKem.X86_64.pa s src, n⟩ ⟨VG.Proof.MlKem.X86_64.pa s dst, n⟩) :
    WP isa (copy dst src n) s fun s' =>
      bytesAt s'.mem (VG.Proof.MlKem.X86_64.pa s dst) n = bytesAt s.mem (VG.Proof.MlKem.X86_64.pa s src) n ∧ Frame [⟨VG.Proof.MlKem.X86_64.pa s dst, n⟩] s.mem s'.mem ∧
        Keep [.rax, .rcx, .rsi, .rdi] s s' := by
  unfold copy lea
  refine WP.seq (WP.mono (WP.keep [.rdi, .rsi, .rcx] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rdi = VG.Proof.MlKem.X86_64.pa s dst ∧
      s'.gpr .rsi = VG.Proof.MlKem.X86_64.pa s src ∧ s'.gpr .rcx = BitVec.ofNat 64 n)
    (by xrun [sx_ofNat hd, sx_ofNat hs, hsr, List.cons_append, List.nil_append, VG.Proof.MlKem.X86_64.sw_ofNat (show n < 2 ^ 32 by omega)])
    (by rfl)) fun s1 ⟨⟨hm1, hdi1, hsi1, hcx1⟩, k1⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .rcx) (N := n) (by omega) hn0 (fun k s' =>
      s'.gpr .rdi = VG.Proof.MlKem.X86_64.pa s dst + BitVec.ofNat 64 k ∧ s'.gpr .rsi = VG.Proof.MlKem.X86_64.pa s src + BitVec.ofNat 64 k ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨VG.Proof.MlKem.X86_64.pa s dst, n⟩] s.mem s'.mem ∧
      (∀ j < k, s'.mem (VG.Proof.MlKem.X86_64.pa s dst + BitVec.ofNat 64 j) = s.mem (VG.Proof.MlKem.X86_64.pa s src + BitVec.ofNat 64 j)) ∧
      Keep [.rax, .rcx, .rsi, .rdi] s s')
    (fun k hk s' ⟨hdi, hsi, hrd', hwr', hf, hc, kk⟩ _ => ?_) (fun _ h => h)
    ⟨by rw [hdi1]; simp, by rw [hsi1]; simp, k1.2.1, k1.2.2, by rw [hm1]; exact Frame.refl _ _,
      fun j hj => absurd hj (Nat.not_lt_zero _), k1.mono (by decide)⟩ hcx1)
    fun s' ⟨_, _, _, _, hf, hc, kk⟩ => ⟨?_, hf, kk⟩
  · refine WP.mono (VG.Proof.MlKem.X86_64.copyBody_ok s' (by rw [hrd', hwr', hsi]; exact VG.Proof.MlKem.X86_64.inRegions_byte hrd hk (by omega))
      (by rw [hwr', hdi]; exact VG.Proof.MlKem.X86_64.inRegions_byte hwr hk (by omega))) fun s'' ⟨⟨hm, hdi', hsi', hcx, hz⟩, k'⟩ =>
        ⟨⟨by rw [hdi', hdi, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, VG.Proof.MlKem.X86_64.off_add],
          by rw [hsi', hsi, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, VG.Proof.MlKem.X86_64.off_add],
          k'.2.1.trans hrd', k'.2.2.trans hwr', ?_, fun j hj => ?_, (kk.trans k').mono (by decide)⟩, hcx, hz⟩
    · rw [hm, hdi]
      exact hf.writeW (List.mem_singleton_self _) _ (contains_offset' (by omega) (by omega))
    · have hsrc : s'.mem (VG.Proof.MlKem.X86_64.pa s src + BitVec.ofNat 64 k) = s.mem (VG.Proof.MlKem.X86_64.pa s src + BitVec.ofNat 64 k) :=
        hf.bytes (R := ⟨VG.Proof.MlKem.X86_64.pa s src, n⟩) (by simpa using hdj) (show n ≤ 2 ^ 64 by omega) hk
      rw [hm, hdi, hsi, VG.WriteBytes.writeW8_apply]
      by_cases e : j = k
      · subst e; rw [ifp rfl, hsrc]
      · rw [ifn (fun h => e (by have := congrArg BitVec.toNat h; simp at this; omega)), hc j (by omega)]
  · simp only [bytesAt]
    exact List.map_congr_left fun i hi => hc i (List.mem_range.mp hi)

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.Rel`. -/
section

/-!
# ML-KEM on x86-64: constant time by relating two runs

The functions that call `vg_mlkem_sample_ntt`, or run its loop, are proven
constant time piece by piece (`RelCT`, see `Proof/Framework/RelCT.lean`): two
runs from entry states `σ₁`, `σ₂` that satisfy the precondition and agree on
the public data are related, between the pieces, by the invariant `I` of the
correctness proof holding of each (`Rel2`). Each piece leaks the same in both
runs (by the taint analysis from registers that `I` says hold the same public
values, `taintRel`, or by a callee's proof, `RelCT.callEx`), and correctness
gives the next invariant (`relInv`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

/-- Two states each related by `I` to an entry state; the entry states
satisfy `Pre` and agree by `Pub`. -/
def Rel2 (Pre : VG.X86_64.State → Prop) (Pub : VG.X86_64.State → VG.X86_64.State → Prop) (I : VG.X86_64.State → VG.X86_64.State → Prop) (s₁ s₂ : VG.X86_64.State) : Prop :=
  ∃ σ₁ σ₂, Pre σ₁ ∧ Pre σ₂ ∧ Pub σ₁ σ₂ ∧ I σ₁ s₁ ∧ I σ₂ s₂

/-- A piece that leaks the same from states related by `I`, and takes each
run from `I` to `I'`. -/
theorem relInv {Pre : VG.X86_64.State → Prop} {Pub : VG.X86_64.State → VG.X86_64.State → Prop} {I I' : VG.X86_64.State → VG.X86_64.State → Prop}
    {c : Prog isa} (hw : ∀ σ s, Pre σ → I σ s → WP isa c s (I' σ))
    (ht : RelCT isa (VG.Proof.MlKem.X86_64.Rel2 Pre Pub I) c fun _ _ => True) :
    RelCT isa (VG.Proof.MlKem.X86_64.Rel2 Pre Pub I) c (VG.Proof.MlKem.X86_64.Rel2 Pre Pub I') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', -⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨σ₁, σ₂, p₁, p₂, hpub, i₁, i₂⟩ := hr
  obtain ⟨_, u₁, f₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', σ₁, σ₂, p₁, p₂, hpub, g₁, g₂⟩

/-- Constant time, from a relation of the runs from the entry states. -/
theorem relStart {Pre : VG.X86_64.State → Prop} {Pub : VG.X86_64.State → VG.X86_64.State → Prop} {c : Prog isa} {Q : VG.X86_64.State → VG.X86_64.State → Prop}
    (h : RelCT isa (VG.Proof.MlKem.X86_64.Rel2 Pre Pub fun σ s => s = σ) c Q) : ConstantTime isa Pre Pub c :=
  RelCT.constantTime (RelCT.mono h (fun s₁ s₂ ⟨p₁, p₂, hp⟩ => ⟨s₁, s₂, p₁, p₂, hp, rfl, rfl⟩) fun _ _ h => h)

/-- Code the taint analysis proves constant time from the registers `rs`,
which hold the same values in runs related by `P`. -/
theorem taintRel {P : VG.X86_64.State → VG.X86_64.State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (X86_64.Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (X86_64.Taint.ofRegs rs) (fun x y hp => X86_64.Taint.agree_ofRegs (hr x y hp)) h

/-- The final states of two runs related by `P` satisfy what correctness
says of each, from its own initial state. -/
theorem RelCT.postDep {P Q : VG.X86_64.State → VG.X86_64.State → Prop} {c : Prog isa} {F : VG.X86_64.State → VG.X86_64.State → Prop}
    (h : RelCT isa P c fun _ _ => True) (hw : ∀ x y, P x y → WP isa c x (F x) ∧ WP isa c y (F y))
    (hQ : ∀ x y x' y', P x y → F x x' → F y y' → Q x' y') : RelCT isa P c Q :=
  RelCT.mono (RelCT.wpDep h hw) (fun _ _ h => h) fun _ _ ⟨_, _, _, hp, f₁, f₂⟩ => hQ _ _ _ _ hp f₁ f₂

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.SampleNtt`. -/
section

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt`, correctness

The function runs in pieces, each from a state satisfying an invariant (`I1` …
`I6`, relative to the entry state `σ`) to the next. `snSample n` runs the
three calls of the sponge, whose output is `XOF(B, 3 n)` (`xof_eq`), and the
loop, which then samples `sampleAfter [] (xofByte B) n` (`sample_ok`). After
168 iterations these are `sampleAfter [] (xofByte B) 280` if there are 256 of
them (`sampleAfter_full`), and otherwise the function runs the 280 iterations
(`more_ok`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)

/-- `vg_mlkem_sample_ntt(seed = rdi, a = rsi, scratch = rdx) -> eax`, with
16 bytes of stack below `rsp`. -/
def sampleK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 34⟩] ∧ s.wr = [pR (s.gpr .rsi), ⟨s.gpr .rdx, 2048⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 34⟩ (pR (s.gpr .rsi)) ∧ Region.Disjoint ⟨s.gpr .rdi, 34⟩ ⟨s.gpr .rdx, 2048⟩ ∧
    (pR (s.gpr .rsi)).Disjoint ⟨s.gpr .rdx, 2048⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 34⟩ ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 2048⟩ ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdi, 34⟩ ∧ (below (s.gpr .rsp) 16).Disjoint (pR (s.gpr .rsi)) ∧
    (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rdx, 2048⟩ ∧ (s.gpr .rdx).toNat + 2048 ≤ 2 ^ 64
  post s s' :=
    (s'.gpr .rax).setWidth 32 = (if (sampleNTT minIterations (bytesAt s.mem (s.gpr .rdi) 34)).isSome then 1 else 0) ∧
      ∀ f, sampleNTT minIterations (bytesAt s.mem (s.gpr .rdi) 34) = some f → PolyIs s'.mem (s.gpr .rsi) f
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ bytesAt s₁.mem (s₁.gpr .rdi) 34 = bytesAt s₂.mem (s₂.gpr .rdi) 34

namespace SampleNtt

theorem sx200 : BitVec.signExtend 64 (200 : BitVec 32) = BitVec.ofNat 64 200 := by decide
theorem sx840 : BitVec.signExtend 64 (840 : BitVec 32) = BitVec.ofNat 64 840 := by decide

theorem r12_not {r : Reg} (hr : r ∈ [Reg.r12, .r13, .r14, .r15]) :
    r ∉ [Reg.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> decide

section
variable (σ : State)
abbrev sd : Addr := σ.gpr .rdi
abbrev aP : Addr := σ.gpr .rsi
abbrev scr : Addr := σ.gpr .rdx
/-- The seed. -/
abbrev B : List Byte := bytesAt σ.mem (VG.Proof.MlKem.X86_64.SampleNtt.sd σ) 34
abbrev scrR : Region := ⟨VG.Proof.MlKem.X86_64.SampleNtt.scr σ, 2048⟩
/-- `scratch + off`. -/
abbrev at' (off : Nat) : Addr := VG.Proof.MlKem.X86_64.SampleNtt.scr σ + BitVec.ofNat 64 off
end

/-- What holds between the pieces. -/
structure Env (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rbx : s.gpr .rbx = VG.Proof.MlKem.X86_64.SampleNtt.scr σ
  rbp : s.gpr .rbp = VG.Proof.MlKem.X86_64.SampleNtt.aP σ
  rsp : s.gpr .rsp = σ.gpr .rsp
  cs : ∀ r ∈ [Reg.r12, .r13, .r14, .r15], s.gpr r = σ.gpr r
  saved : s.mem.readW (VG.Proof.MlKem.X86_64.SampleNtt.at' σ 1680) 64 = σ.gpr .rbx ∧ s.mem.readW (VG.Proof.MlKem.X86_64.SampleNtt.at' σ 1688) 64 = σ.gpr .rbp ∧
    s.mem.readW (VG.Proof.MlKem.X86_64.SampleNtt.at' σ 1696) 64 = VG.Proof.MlKem.X86_64.SampleNtt.sd σ
  frame : Frame [pR (VG.Proof.MlKem.X86_64.SampleNtt.aP σ), VG.Proof.MlKem.X86_64.SampleNtt.scrR σ, below (σ.gpr .rsp) 16] σ.mem s.mem

section
variable {σ : State} (hp : sampleK.pre σ)
include hp

theorem sub_scr {a n : Nat} (h : a + n ≤ 2048) : Region.Sub ⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ a, n⟩ (VG.Proof.MlKem.X86_64.SampleNtt.scrR σ) :=
  sub_offset' h (by have := hp.2.2.2.2.2.2.2.2.2.2.2; omega)

omit hp in
theorem sub_scr0 {n : Nat} (h : n ≤ 2048) : Region.Sub ⟨VG.Proof.MlKem.X86_64.SampleNtt.scr σ, n⟩ (VG.Proof.MlKem.X86_64.SampleNtt.scrR σ) := Region.sub_prefix h

omit hp in
theorem disj_scr {a n b m : Nat} (h : a + n ≤ b) (hb : b + m ≤ 2048) :
    Region.Disjoint ⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ a, n⟩ ⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ b, m⟩ := off_disj h (by omega)

omit hp in
theorem disj_scr0 {n b m : Nat} (h : n ≤ b) (hb : b + m ≤ 2048) :
    Region.Disjoint ⟨VG.Proof.MlKem.X86_64.SampleNtt.scr σ, n⟩ ⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ b, m⟩ := by
  have := VG.Proof.MlKem.X86_64.SampleNtt.disj_scr (σ := σ) (a := 0) (n := n) (by omega) hb
  simpa [VG.Proof.MlKem.X86_64.SampleNtt.at', add_ofNat_zero] using this

/-- A sub-region of the scratch space is apart from the seed. -/
theorem seed_scr {a n : Nat} (h : a + n ≤ 2048) : Region.Disjoint ⟨VG.Proof.MlKem.X86_64.SampleNtt.sd σ, 34⟩ ⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ a, n⟩ :=
  hp.2.2.2.1.sub_right (VG.Proof.MlKem.X86_64.SampleNtt.sub_scr hp h)

theorem stk_scr {a n : Nat} (h : a + n ≤ 2048) : (below (σ.gpr .rsp) 16).Disjoint ⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ a, n⟩ :=
  hp.2.2.2.2.2.2.2.2.2.2.1.sub_right (VG.Proof.MlKem.X86_64.SampleNtt.sub_scr hp h)

theorem seed_scr0 {n : Nat} (h : n ≤ 2048) : Region.Disjoint ⟨VG.Proof.MlKem.X86_64.SampleNtt.sd σ, 34⟩ ⟨VG.Proof.MlKem.X86_64.SampleNtt.scr σ, n⟩ :=
  hp.2.2.2.1.sub_right (VG.Proof.MlKem.X86_64.SampleNtt.sub_scr0 h)

theorem stk_scr0 {n : Nat} (h : n ≤ 2048) : (below (σ.gpr .rsp) 16).Disjoint ⟨VG.Proof.MlKem.X86_64.SampleNtt.scr σ, n⟩ :=
  hp.2.2.2.2.2.2.2.2.2.2.1.sub_right (VG.Proof.MlKem.X86_64.SampleNtt.sub_scr0 h)

/-- The seed is not written. -/
theorem seed_frame {s : State} (he : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s) : bytesAt s.mem (VG.Proof.MlKem.X86_64.SampleNtt.sd σ) 34 = VG.Proof.MlKem.X86_64.SampleNtt.B σ :=
  bytesAt_frame he.frame (by simpa using ⟨hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.2.2.2.2.1.symm⟩) (by decide)

theorem low_sub {a n : Nat} (h : a + n ≤ 1680) : Region.Sub ⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ a, n⟩ ⟨VG.Proof.MlKem.X86_64.SampleNtt.scr σ, 1680⟩ :=
  sub_offset' h (by have := hp.2.2.2.2.2.2.2.2.2.2.2; omega)

omit hp in
/-- The values saved in `scratch[1680..1704)` are kept by writes apart from them. -/
theorem Env.saved_frame {s s' : State} (he : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s) {rs : List Region}
    (hd : ∀ k, 1680 ≤ k → k + 8 ≤ 2048 → ∀ r ∈ rs, (⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ k, 8⟩ : Region).Disjoint r)
    (hf : Frame rs s.mem s'.mem) :
    s'.mem.readW (VG.Proof.MlKem.X86_64.SampleNtt.at' σ 1680) 64 = σ.gpr .rbx ∧ s'.mem.readW (VG.Proof.MlKem.X86_64.SampleNtt.at' σ 1688) 64 = σ.gpr .rbp ∧
      s'.mem.readW (VG.Proof.MlKem.X86_64.SampleNtt.at' σ 1696) 64 = VG.Proof.MlKem.X86_64.SampleNtt.sd σ := by
  rw [hf.readW (Region.contains_self _ _) (hd 1680 (by omega) (by omega)) (by decide),
    hf.readW (Region.contains_self _ _) (hd 1688 (by omega) (by omega)) (by decide),
    hf.readW (Region.contains_self _ _) (hd 1696 (by omega) (by omega)) (by decide)]
  exact he.saved

/-- A call that writes within the first 1680 bytes of the scratch space and
the stack keeps `Env`. -/
theorem Env.call {s s' : State} (he : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s) {rs : List Region} (hrs : ∀ r ∈ rs, Region.Sub r ⟨VG.Proof.MlKem.X86_64.SampleNtt.scr σ, 1680⟩)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hf : Frame (rs ++ [below (s.gpr .rsp) 16]) s.mem s'.mem) : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s' := by
  have hsp : s'.gpr .rsp = s.gpr .rsp := hcs .rsp (by simp [calleeSaved])
  have hd : ∀ k, 1680 ≤ k → k + 8 ≤ 2048 → ∀ r ∈ rs ++ [below (s.gpr .rsp) 16],
      (⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ k, 8⟩ : Region).Disjoint r := by
    intro k hk hk' r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact ((VG.Proof.MlKem.X86_64.SampleNtt.disj_scr0 (σ := σ) (n := 1680) (b := k) (m := 8) hk hk').symm).sub_right (hrs r hr)
    · simp only [List.mem_singleton] at hr; subst hr
      rw [he.rsp]; exact (VG.Proof.MlKem.X86_64.SampleNtt.stk_scr hp hk').symm
  refine ⟨hrd.trans he.rd, hwr.trans he.wr, by rw [hcs .rbx (by simp [calleeSaved]), he.rbx],
    by rw [hcs .rbp (by simp [calleeSaved]), he.rbp], by rw [hsp, he.rsp], fun r hr => ?_, ?_, ?_⟩
  · have hr' : r ∈ calleeSaved := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide
    rw [hcs r hr', he.cs r hr]
  · exact he.saved_frame hd hf
  · refine he.frame.trans (hf.sub fun r hr => ?_)
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨VG.Proof.MlKem.X86_64.SampleNtt.scrR σ, by simp, fun x h => VG.Proof.MlKem.X86_64.SampleNtt.sub_scr0 (σ := σ) (n := 1680) (by omega) x (hrs r hr x h)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨below (σ.gpr .rsp) 16, by simp, by rw [he.rsp]; exact fun _ h => h⟩

/-! ## The prologue -/

/-- The arguments of `absorb`, after zeroing the state. -/
structure I1 (σ s : State) : Prop where
  env : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s
  zero : stateAt s.mem (VG.Proof.MlKem.X86_64.SampleNtt.scr σ) = Spec.Sha3.zero
  args : VG.Proof.MlKem.X86_64.AbsorbArgs s (VG.Proof.MlKem.X86_64.SampleNtt.scr σ) (VG.Proof.MlKem.X86_64.SampleNtt.sd σ) (VG.Proof.MlKem.X86_64.SampleNtt.at' σ 200) 168 0 34

theorem inScr {s : State} (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 2048) :
    InRegions s.wr (VG.Proof.MlKem.X86_64.SampleNtt.scr σ + BitVec.ofNat 64 a) n := by
  rw [hw, hp.2.1]
  exact ⟨VG.Proof.MlKem.X86_64.SampleNtt.scrR σ, by simp, contains_offset' h (by omega)⟩

omit hp in
/-- `Env` after a block that writes only caller-saved registers and no memory. -/
theorem Env.keep {s s' : State} (he : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s) (hm : s'.mem = s.mem)
    (hk : Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] s s') : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s' :=
  ⟨hk.2.1.trans he.rd, hk.2.2.trans he.wr, by rw [hk.gpr (by decide), he.rbx], by rw [hk.gpr (by decide), he.rbp],
    by rw [hk.gpr (by decide), he.rsp], fun r hr => by rw [hk.gpr (VG.Proof.MlKem.X86_64.SampleNtt.r12_not hr), he.cs r hr],
    by rw [hm]; exact he.saved, by rw [hm]; exact he.frame⟩

/-- The seed and the scratch space in the regions. -/
theorem regions {s : State} (he : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s) : s.rd ++ s.wr = [⟨VG.Proof.MlKem.X86_64.SampleNtt.sd σ, 34⟩, pR (VG.Proof.MlKem.X86_64.SampleNtt.aP σ), VG.Proof.MlKem.X86_64.SampleNtt.scrR σ] := by
  rw [he.rd, he.wr, hp.1, hp.2.1]; rfl

theorem cov_scr {s : State} (he : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ off, r.base = VG.Proof.MlKem.X86_64.SampleNtt.scr σ + BitVec.ofNat 64 off ∧ off + r.len ≤ 2048) : Covers rs s.wr :=
  Covers.of_sub fun r hr => by
    obtain ⟨off, hb, hl⟩ := h r hr
    exact ⟨VG.Proof.MlKem.X86_64.SampleNtt.scrR σ, by rw [he.wr, hp.2.1]; simp, off, hb, hl⟩

theorem cov_all {s : State} (he : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s) {rs : List Region}
    (h : ∀ r ∈ rs, r = ⟨VG.Proof.MlKem.X86_64.SampleNtt.sd σ, 34⟩ ∨ ∃ off, r.base = VG.Proof.MlKem.X86_64.SampleNtt.scr σ + BitVec.ofNat 64 off ∧ off + r.len ≤ 2048) :
    Covers rs (s.rd ++ s.wr) :=
  Covers.of_sub fun r hr => by
    rw [VG.Proof.MlKem.X86_64.SampleNtt.regions hp he]
    rcases h r hr with rfl | ⟨off, hb, hl⟩
    · exact ⟨⟨VG.Proof.MlKem.X86_64.SampleNtt.sd σ, 34⟩, by simp, 0, (add_ofNat_zero _).symm, by simp⟩
    · exact ⟨VG.Proof.MlKem.X86_64.SampleNtt.scrR σ, by simp, off, hb, hl⟩


/-- Zeroing the state, and the arguments of `absorb`, from `rcx` = `seed`. -/
theorem abs_ok {s : State} (he : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s) (hcx : s.gpr .rcx = VG.Proof.MlKem.X86_64.SampleNtt.sd σ) : WP isa (.block snAbs) s (VG.Proof.MlKem.X86_64.SampleNtt.I1 σ) := by
  unfold snAbs
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rax = 0) (by xrun) (by decide))
    fun s1 ⟨⟨hm1, hax⟩, k1⟩ => ?_
  have he1 := he.keep hm1 (k1.mono (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (zeroSt_ok .rbx 0 s1 hax fun i hi => by
      rw [he1.rbx, add_ofNat_zero]; exact VG.Proof.MlKem.X86_64.SampleNtt.inScr hp he1.wr (by omega)) fun s2 ⟨hz, hf2, k2⟩ => ?_
  rw [he1.rbx, add_ofNat_zero] at hz hf2
  have he2 : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s2 := Env.call hp he1 (rs := [⟨VG.Proof.MlKem.X86_64.SampleNtt.scr σ, 200⟩])
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega))
    k2.2.1 k2.2.2 (fun r _ => k2.gpr (by simp)) (hf2.mono (by simp))
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .r8, .r9] (Q := fun s => s.mem = s2.mem ∧
      s.gpr .rdi = VG.Proof.MlKem.X86_64.SampleNtt.scr σ ∧ s.gpr .rsi = BitVec.ofNat 64 168 ∧ s.gpr .rdx = BitVec.ofNat 64 0 ∧
      s.gpr .r8 = BitVec.ofNat 64 34 ∧ s.gpr .r9 = VG.Proof.MlKem.X86_64.SampleNtt.at' σ 200)
    (by xrun [he2.rbx, VG.Proof.MlKem.X86_64.SampleNtt.sx200]) (by decide)) fun s3 ⟨⟨hm3, hdi, hsi, hdx, h8, h9⟩, k3⟩ => ?_
  have he3 := he2.keep hm3 (k3.mono (by decide))
  refine ⟨he3, by rw [hm3]; exact hz,
    ⟨hdi, hsi, hdx, by rw [k3.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide), hcx], h8, h9, by decide,
      by decide, by decide, VG.Proof.MlKem.X86_64.SampleNtt.disj_scr0 (by omega) (by omega), VG.Proof.MlKem.X86_64.SampleNtt.seed_scr0 hp (by omega), VG.Proof.MlKem.X86_64.SampleNtt.seed_scr hp (by omega),
      by rw [he3.rsp]; exact VG.Proof.MlKem.X86_64.SampleNtt.stk_scr0 hp (by omega), by rw [he3.rsp]; exact hp.2.2.2.2.2.2.2.2.1,
      by rw [he3.rsp]; exact VG.Proof.MlKem.X86_64.SampleNtt.stk_scr hp (by omega)⟩⟩

theorem proA_ok : WP isa (.block snPro) σ (VG.Proof.MlKem.X86_64.SampleNtt.I1 σ) := by
  unfold snPro
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rbx, .rbp, .rcx] (Q := fun s =>
      s.mem = ((σ.mem.writeW (VG.Proof.MlKem.X86_64.SampleNtt.at' σ 1680) (σ.gpr .rbx)).writeW (VG.Proof.MlKem.X86_64.SampleNtt.at' σ 1688) (σ.gpr .rbp)).writeW (VG.Proof.MlKem.X86_64.SampleNtt.at' σ 1696)
          (σ.gpr .rdi) ∧
        s.gpr .rbx = VG.Proof.MlKem.X86_64.SampleNtt.scr σ ∧ s.gpr .rbp = VG.Proof.MlKem.X86_64.SampleNtt.aP σ ∧ s.gpr .rcx = VG.Proof.MlKem.X86_64.SampleNtt.sd σ)
    (by xrun [VG.Proof.MlKem.X86_64.SampleNtt.inScr hp rfl (a := 1680) (n := 8) (by omega), VG.Proof.MlKem.X86_64.SampleNtt.inScr hp rfl (a := 1688) (n := 8) (by omega),
      VG.Proof.MlKem.X86_64.SampleNtt.inScr hp rfl (a := 1696) (n := 8) (by omega)])
    (by decide)) fun s1 ⟨⟨hm1, hbx, hbp, hcx⟩, k1⟩ => VG.Proof.MlKem.X86_64.SampleNtt.abs_ok hp ?_ hcx
  have sep : ∀ a b, a + 8 ≤ b → b + 8 ≤ 2048 →
      Mem.Sep (VG.Proof.MlKem.X86_64.SampleNtt.at' σ a) (64 / 8) (VG.Proof.MlKem.X86_64.SampleNtt.at' σ b) (64 / 8) ∧ Mem.Sep (VG.Proof.MlKem.X86_64.SampleNtt.at' σ b) (64 / 8) (VG.Proof.MlKem.X86_64.SampleNtt.at' σ a) (64 / 8) :=
    fun a b h hb => ⟨(VG.Proof.MlKem.X86_64.SampleNtt.disj_scr (σ := σ) (n := 8) (m := 8) h hb).sep (Region.contains_self _ _)
      (Region.contains_self _ _), (VG.Proof.MlKem.X86_64.SampleNtt.disj_scr (σ := σ) (n := 8) (m := 8) h hb).symm.sep (Region.contains_self _ _)
      (Region.contains_self _ _)⟩
  have hin : ∀ a, a + 8 ≤ 2048 → (VG.Proof.MlKem.X86_64.SampleNtt.scrR σ).Contains (VG.Proof.MlKem.X86_64.SampleNtt.at' σ a) (64 / 8) := fun a ha =>
    contains_offset' (by omega) (by omega)
  refine ⟨k1.2.1, k1.2.2, hbx, hbp, k1.gpr (by decide), fun r hr => k1.gpr (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide), ?_, ?_⟩
  · rw [hm1, Mem.readW_writeW_sep (sep 1680 1696 (by omega) (by omega)).1 (by decide),
      Mem.readW_writeW_sep (sep 1680 1688 (by omega) (by omega)).1 (by decide), Mem.readW_writeW_self64,
      Mem.readW_writeW_sep (sep 1688 1696 (by omega) (by omega)).1 (by decide), Mem.readW_writeW_self64,
      Mem.readW_writeW_self64]
    exact ⟨rfl, rfl, rfl⟩
  · rw [hm1]
    exact (((Frame.refl _ _).writeW (by simp) _ (hin 1680 (by omega))).writeW (by simp) _
      (hin 1688 (by omega))).writeW (by simp) _ (hin 1696 (by omega))

/-! ## The sponge -/

/-- After absorbing the seed. -/
structure I2 (σ s : State) : Prop where
  env : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s
  repr : Spec.Sha3.Repr s.mem (VG.Proof.MlKem.X86_64.SampleNtt.scr σ) 168 (VG.Proof.MlKem.X86_64.SampleNtt.B σ)

theorem covA {s : State} (he : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s) :
    Covers ([⟨VG.Proof.MlKem.X86_64.SampleNtt.sd σ, 34⟩] ++ [⟨VG.Proof.MlKem.X86_64.SampleNtt.scr σ, 200⟩, ⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ 200, 640⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨VG.Proof.MlKem.X86_64.SampleNtt.scr σ, 200⟩, ⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ 200, 640⟩] s.wr := by
  refine ⟨VG.Proof.MlKem.X86_64.SampleNtt.cov_all hp he ?_, VG.Proof.MlKem.X86_64.SampleNtt.cov_scr hp he ?_⟩
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [.inl rfl, .inr ⟨0, (add_ofNat_zero _).symm, by simp⟩, .inr ⟨200, rfl, by simp⟩]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [⟨0, (add_ofNat_zero _).symm, by simp⟩, ⟨200, rfl, by simp⟩]

theorem subA : ∀ r ∈ [(⟨VG.Proof.MlKem.X86_64.SampleNtt.scr σ, 200⟩ : Region), ⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ 200, 640⟩], Region.Sub r ⟨VG.Proof.MlKem.X86_64.SampleNtt.scr σ, 1680⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [Region.sub_prefix (by omega), VG.Proof.MlKem.X86_64.SampleNtt.low_sub hp (by omega)]

theorem callB_ok {s : State} (h : VG.Proof.MlKem.X86_64.SampleNtt.I1 σ s) : WP isa (.call "vg_keccak_absorb_scratch" Impl.Sha3.X86_64.Stream.absorb) s (VG.Proof.MlKem.X86_64.SampleNtt.I2 σ) := by
  refine VG.Proof.MlKem.X86_64.absorb_call h.args (VG.Proof.MlKem.X86_64.SampleNtt.covA hp h.env).1 (VG.Proof.MlKem.X86_64.SampleNtt.covA hp h.env).2 fun s' hrd hwr hcs hf hr _ =>
    ⟨Env.call hp h.env (VG.Proof.MlKem.X86_64.SampleNtt.subA hp) hrd hwr hcs hf, ?_⟩
  have := hr [] (Proof.MlKem.repr_nil h.zero) rfl
  rwa [List.nil_append, VG.Proof.MlKem.X86_64.SampleNtt.seed_frame hp h.env] at this

/-- The arguments of `pad`. -/
structure I3 (σ s : State) : Prop where
  env : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s
  repr : Spec.Sha3.Repr s.mem (VG.Proof.MlKem.X86_64.SampleNtt.scr σ) 168 (VG.Proof.MlKem.X86_64.SampleNtt.B σ)
  args : VG.Proof.MlKem.X86_64.PadArgs s (VG.Proof.MlKem.X86_64.SampleNtt.scr σ) (VG.Proof.MlKem.X86_64.SampleNtt.at' σ 200) 168 34
  rcx : (s.gpr .rcx).setWidth 8 = Spec.Sha3.shakeSuffix

theorem blkC_ok {s : State} (h : VG.Proof.MlKem.X86_64.SampleNtt.I2 σ s) : WP isa (.block snPadArgs) s (VG.Proof.MlKem.X86_64.SampleNtt.I3 σ) := by
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rdi = VG.Proof.MlKem.X86_64.SampleNtt.scr σ ∧ s'.gpr .rsi = BitVec.ofNat 64 168 ∧ s'.gpr .rdx = BitVec.ofNat 64 34 ∧
      s'.gpr .rcx = BitVec.setWidth 64 (0x1f : BitVec 32) ∧ s'.gpr .r8 = VG.Proof.MlKem.X86_64.SampleNtt.at' σ 200)
    (by unfold snPadArgs; xrun [h.env.rbx, VG.Proof.MlKem.X86_64.SampleNtt.sx200]) (by decide)) fun s' ⟨⟨hm, hdi, hsi, hdx, hcx, h8⟩, k⟩ => ?_
  have he := h.env.keep hm (k.mono (by decide))
  refine ⟨he, by rw [hm]; exact h.repr, ⟨hdi, hsi, hdx, h8, by decide, by decide, VG.Proof.MlKem.X86_64.SampleNtt.disj_scr0 (by omega) (by omega),
    by rw [he.rsp]; exact VG.Proof.MlKem.X86_64.SampleNtt.stk_scr0 hp (by omega), by rw [he.rsp]; exact VG.Proof.MlKem.X86_64.SampleNtt.stk_scr hp (by omega)⟩, by rw [hcx]; decide⟩

/-- After padding. -/
structure I4 (σ s : State) : Prop where
  env : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s
  st : stateAt s.mem (VG.Proof.MlKem.X86_64.SampleNtt.scr σ) = Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (VG.Proof.MlKem.X86_64.SampleNtt.B σ)

theorem covP {s : State} (he : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s) :
    Covers ([] ++ [⟨VG.Proof.MlKem.X86_64.SampleNtt.scr σ, 200⟩, ⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ 200, 640⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨VG.Proof.MlKem.X86_64.SampleNtt.scr σ, 200⟩, ⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ 200, 640⟩] s.wr :=
  ⟨fun a n h => (VG.Proof.MlKem.X86_64.SampleNtt.covA hp he).1 a n (by simp only [List.nil_append] at h; exact
                                    ⟨_, List.mem_append_right _ h.choose_spec.1, h.choose_spec.2⟩), (VG.Proof.MlKem.X86_64.SampleNtt.covA hp he).2⟩

theorem callD_ok {s : State} (h : VG.Proof.MlKem.X86_64.SampleNtt.I3 σ s) : WP isa (.call "vg_keccak_pad_scratch" Impl.Sha3.X86_64.Stream.pad) s (VG.Proof.MlKem.X86_64.SampleNtt.I4 σ) := by
  refine VG.Proof.MlKem.X86_64.pad_call h.args (VG.Proof.MlKem.X86_64.SampleNtt.covP hp h.env).1 (VG.Proof.MlKem.X86_64.SampleNtt.covP hp h.env).2 fun s' hrd hwr hcs hf hst =>
    ⟨Env.call hp h.env (VG.Proof.MlKem.X86_64.SampleNtt.subA hp) hrd hwr hcs hf, ?_⟩
  rw [hst (VG.Proof.MlKem.X86_64.SampleNtt.B σ) h.repr (by rw [bytesAt_length]), h.rcx]

/-- The arguments of `squeeze`, for `len` bytes. -/
structure I5 (σ : State) (len : Nat) (s : State) : Prop where
  env : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s
  st : stateAt s.mem (VG.Proof.MlKem.X86_64.SampleNtt.scr σ) = Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (VG.Proof.MlKem.X86_64.SampleNtt.B σ)
  args : VG.Proof.MlKem.X86_64.SqueezeArgs s (VG.Proof.MlKem.X86_64.SampleNtt.scr σ) (VG.Proof.MlKem.X86_64.SampleNtt.at' σ 840) (VG.Proof.MlKem.X86_64.SampleNtt.at' σ 200) 168 0 len

theorem blkE_ok {n : BitVec 32} {len : Nat} (hn : (3 * n).toNat = len) (hl : len ≤ 840) {s : State} (h : VG.Proof.MlKem.X86_64.SampleNtt.I4 σ s) :
    WP isa (.block (snSqzArgs (3 * n))) s (VG.Proof.MlKem.X86_64.SampleNtt.I5 σ len) := by
  refine WP.mono (WP.keep [.rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rdi = VG.Proof.MlKem.X86_64.SampleNtt.scr σ ∧ s'.gpr .rsi = BitVec.ofNat 64 168 ∧ s'.gpr .rdx = BitVec.ofNat 64 0 ∧
      s'.gpr .rcx = VG.Proof.MlKem.X86_64.SampleNtt.at' σ 840 ∧ s'.gpr .r8 = BitVec.setWidth 64 (3 * n) ∧ s'.gpr .r9 = VG.Proof.MlKem.X86_64.SampleNtt.at' σ 200)
    (by unfold snSqzArgs; xrun [h.env.rbx, VG.Proof.MlKem.X86_64.SampleNtt.sx200, VG.Proof.MlKem.X86_64.SampleNtt.sx840]) rfl)
    fun s' ⟨⟨hm, hdi, hsi, hdx, hcx, h8, h9⟩, k⟩ => ?_
  have he := h.env.keep hm (k.mono (by decide))
  rw [← BitVec.ofNat_toNat, hn] at h8
  refine ⟨he, by rw [hm]; exact h.st, ⟨hdi, hsi, hdx, hcx, h8, h9, by decide, by decide, by omega,
    VG.Proof.MlKem.X86_64.SampleNtt.disj_scr0 (by omega) (by omega), VG.Proof.MlKem.X86_64.SampleNtt.disj_scr0 (by omega) (by omega),
    (VG.Proof.MlKem.X86_64.SampleNtt.disj_scr (σ := σ) (a := 200) (n := 640) (b := 840) (m := len) (by omega) (by omega)).symm,
    by rw [he.rsp]; exact VG.Proof.MlKem.X86_64.SampleNtt.stk_scr0 hp (by omega), by rw [he.rsp]; exact VG.Proof.MlKem.X86_64.SampleNtt.stk_scr hp (by omega),
    by rw [he.rsp]; exact VG.Proof.MlKem.X86_64.SampleNtt.stk_scr hp (by omega)⟩⟩

/-- After squeezing `len` bytes: the XOF output. -/
structure I6 (σ : State) (len : Nat) (s : State) : Prop where
  env : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s
  out : bytesAt s.mem (VG.Proof.MlKem.X86_64.SampleNtt.at' σ 840) len = xof (VG.Proof.MlKem.X86_64.SampleNtt.B σ) len

theorem covS {s : State} (he : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s) {len : Nat} (hl : len ≤ 840) :
    Covers ([] ++ [⟨VG.Proof.MlKem.X86_64.SampleNtt.scr σ, 200⟩, ⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ 840, len⟩, ⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ 200, 640⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨VG.Proof.MlKem.X86_64.SampleNtt.scr σ, 200⟩, ⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ 840, len⟩, ⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ 200, 640⟩] s.wr := by
  refine ⟨VG.Proof.MlKem.X86_64.SampleNtt.cov_all hp he ?_, VG.Proof.MlKem.X86_64.SampleNtt.cov_scr hp he ?_⟩
  · intro r hr
    simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [.inr ⟨0, (add_ofNat_zero _).symm, by simp⟩, .inr ⟨840, rfl, by simp; omega⟩, .inr ⟨200, rfl, by simp⟩]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [⟨0, (add_ofNat_zero _).symm, by simp⟩, ⟨840, rfl, by simp; omega⟩, ⟨200, rfl, by simp⟩]

theorem subS {len : Nat} (hl : len ≤ 840) : ∀ r ∈ [(⟨VG.Proof.MlKem.X86_64.SampleNtt.scr σ, 200⟩ : Region), ⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ 840, len⟩, ⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ 200, 640⟩],
    Region.Sub r ⟨VG.Proof.MlKem.X86_64.SampleNtt.scr σ, 1680⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [Region.sub_prefix (by omega), VG.Proof.MlKem.X86_64.SampleNtt.low_sub hp (by omega), VG.Proof.MlKem.X86_64.SampleNtt.low_sub hp (by omega)]

theorem callF_ok {len : Nat} (hl : len ≤ 840) {s : State} (h : VG.Proof.MlKem.X86_64.SampleNtt.I5 σ len s) :
    WP isa (.call "vg_keccak_squeeze_scratch" Impl.Sha3.X86_64.Stream.squeeze) s (VG.Proof.MlKem.X86_64.SampleNtt.I6 σ len) := by
  refine VG.Proof.MlKem.X86_64.squeeze_call h.args (VG.Proof.MlKem.X86_64.SampleNtt.covS hp h.env hl).1 (VG.Proof.MlKem.X86_64.SampleNtt.covS hp h.env hl).2 fun s' hrd hwr hcs hf ho =>
    ⟨Env.call hp h.env (VG.Proof.MlKem.X86_64.SampleNtt.subS hp hl) hrd hwr hcs hf, ?_⟩
  rw [ho, h.st, xof_eq]

/-! ## The loop -/

/-- The coefficients sampled after `t` iterations. -/
abbrev Lt (σ : State) (t : Nat) : List Zq := sampleAfter [] (xofByte (VG.Proof.MlKem.X86_64.SampleNtt.B σ)) t

/-- At the start of iteration `t` of `N`. -/
structure LAt (σ : State) (N t : Nat) (s : State) : Prop where
  env : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s
  out : bytesAt s.mem (VG.Proof.MlKem.X86_64.SampleNtt.at' σ 840) (3 * N) = xof (VG.Proof.MlKem.X86_64.SampleNtt.B σ) (3 * N)
  rsi : s.gpr .rsi = VG.Proof.MlKem.X86_64.SampleNtt.at' σ 840 + BitVec.ofNat 64 (3 * t)
  rdi : s.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlKem.X86_64.SampleNtt.Lt σ t).length
  rcx : s.gpr .rcx = BitVec.ofNat 64 (N - t)
  stored : VG.Proof.MlKem.X86_64.Stored s.mem (VG.Proof.MlKem.X86_64.SampleNtt.aP σ) (VG.Proof.MlKem.X86_64.SampleNtt.Lt σ t)

omit hp in
theorem out_byte {N t : Nat} {s : State} (h : VG.Proof.MlKem.X86_64.SampleNtt.LAt σ N t s) {k : Nat} (hk : 3 * t + k < 3 * N) :
    s.mem (s.gpr .rsi + BitVec.ofNat 64 k) = xofByte (VG.Proof.MlKem.X86_64.SampleNtt.B σ) (3 * t + k) := by
  have := congrArg (fun L => L.getD (3 * t + k) 0) h.out
  rw [bytesAt_getD _ _ hk, xof_getD _ hk] at this
  rw [h.rsi, VG.Proof.MlKem.X86_64.off_add]; exact this

theorem lat_regions {N t : Nat} (hN : N ≤ 280) {s : State} (h : VG.Proof.MlKem.X86_64.SampleNtt.LAt σ N t s) {k : Nat} (hk : 3 * t + k < 3 * N) :
    InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 k) 1 := by
  rw [VG.Proof.MlKem.X86_64.SampleNtt.regions hp h.env, h.rsi, VG.Proof.MlKem.X86_64.off_add, VG.Proof.MlKem.X86_64.off_add]
  exact ⟨VG.Proof.MlKem.X86_64.SampleNtt.scrR σ, by simp, contains_offset' (by omega) (by omega)⟩

/-- An iteration, from `LAt`. -/
theorem lat_step {N t : Nat} (hN : N ≤ 280) (ht : t < N) {s : State} (h : VG.Proof.MlKem.X86_64.SampleNtt.LAt σ N t s) :
    WP isa snBody s fun s' => VG.Proof.MlKem.X86_64.SampleNtt.LAt σ N (t + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (N - t) - 1 == 0) := by
  have hL : (VG.Proof.MlKem.X86_64.SampleNtt.Lt σ t).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ t
  have hw : pR (VG.Proof.MlKem.X86_64.SampleNtt.aP σ) ∈ s.wr := by rw [h.env.wr, hp.2.1]; simp
  refine WP.mono (VG.Proof.MlKem.X86_64.snBody_ok s (aP := VG.Proof.MlKem.X86_64.SampleNtt.aP σ) h.env.rbp h.rdi hL (WrA.of_mem hw) h.stored
    (by simpa using VG.Proof.MlKem.X86_64.SampleNtt.lat_regions hp hN h (k := 0) (by omega)) (VG.Proof.MlKem.X86_64.SampleNtt.lat_regions hp hN h (by omega))
    (VG.Proof.MlKem.X86_64.SampleNtt.lat_regions hp hN h (by omega))) fun s' ⟨hdi, hst, hf, hsi, hcx, hz, hk⟩ => ?_
  have e0 := VG.Proof.MlKem.X86_64.SampleNtt.out_byte h (k := 0) (by omega)
  rw [add_ofNat_zero, Nat.add_zero] at e0
  rw [e0, VG.Proof.MlKem.X86_64.SampleNtt.out_byte h (k := 1) (by omega), VG.Proof.MlKem.X86_64.SampleNtt.out_byte h (k := 2) (by omega), ← sampleAfter_succ] at hdi hst
  have hd : ∀ r ∈ [pR (VG.Proof.MlKem.X86_64.SampleNtt.aP σ)], (⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ 840, 3 * N⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.2.2.2.2.1.symm.sub_left (VG.Proof.MlKem.X86_64.SampleNtt.sub_scr hp (by omega))
  have dA : ∀ k, 1680 ≤ k → k + 8 ≤ 2048 → ∀ r ∈ [pR (VG.Proof.MlKem.X86_64.SampleNtt.aP σ)], (⟨VG.Proof.MlKem.X86_64.SampleNtt.at' σ k, 8⟩ : Region).Disjoint r :=
    fun k _ hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.2.2.2.2.1.symm.sub_left (VG.Proof.MlKem.X86_64.SampleNtt.sub_scr hp hk)
  have hk' : Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] s s' := hk.mono (by simp)
  refine ⟨⟨⟨hk'.2.1.trans h.env.rd, hk'.2.2.trans h.env.wr, by rw [hk'.gpr (by decide), h.env.rbx],
    by rw [hk'.gpr (by decide), h.env.rbp], by rw [hk'.gpr (by decide), h.env.rsp],
    fun r hr => by rw [hk'.gpr (VG.Proof.MlKem.X86_64.SampleNtt.r12_not hr), h.env.cs r hr], h.env.saved_frame dA hf,
    h.env.frame.trans (hf.mono (by simp))⟩,
    by rw [bytesAt_frame hf hd (by omega)]; exact h.out, by rw [hsi, h.rsi,
      show (3 : BitVec 64) = BitVec.ofNat 64 3 from rfl, VG.Proof.MlKem.X86_64.off_add, Nat.mul_succ], hdi,
    by rw [hcx, h.rcx, ofNat64_pred (by omega) (by omega)]; rfl, hst⟩, by rw [hz, h.rcx]⟩

omit hp in
/-- After the first block of the loop's setup. -/
structure IA (σ : State) (N : Nat) (s : State) : Prop where
  env : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s
  out : bytesAt s.mem (VG.Proof.MlKem.X86_64.SampleNtt.at' σ 840) (3 * N) = xof (VG.Proof.MlKem.X86_64.SampleNtt.B σ) (3 * N)
  rsi : s.gpr .rsi = VG.Proof.MlKem.X86_64.SampleNtt.at' σ 840
  rdi : s.gpr .rdi = 0

omit hp in
theorem latA {N : Nat} {s : State} (h : VG.Proof.MlKem.X86_64.SampleNtt.I6 σ (3 * N) s) :
    WP isa (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 840), .mov32 .rdi (.imm 0)]) s (VG.Proof.MlKem.X86_64.SampleNtt.IA σ N) := by
  refine WP.mono (WP.keep [.rsi, .rdi] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = VG.Proof.MlKem.X86_64.SampleNtt.at' σ 840 ∧ s'.gpr .rdi = 0) (by xrun [h.env.rbx, VG.Proof.MlKem.X86_64.SampleNtt.sx840]) (by decide))
    fun s1 ⟨⟨hm1, hsi1, hdi1⟩, k1⟩ => ?_
  exact ⟨h.env.keep hm1 (k1.mono (by decide)), by rw [hm1]; exact h.out, hsi1, hdi1⟩

omit hp in
theorem latB {n : BitVec 32} {N : Nat} (hn : n.toNat = N) {s : State} (h : VG.Proof.MlKem.X86_64.SampleNtt.IA σ N s) :
    WP isa (.block [.mov32 .rcx (.imm n)]) s (VG.Proof.MlKem.X86_64.SampleNtt.LAt σ N 0) := by
  refine WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rcx = BitVec.setWidth 64 n)
    (by xrun) rfl) fun s2 ⟨⟨hm2, hcx⟩, k2⟩ => ?_
  exact ⟨h.env.keep hm2 (k2.mono (by decide)), by rw [hm2]; exact h.out, by rw [k2.gpr (by decide), h.rsi]; simp,
    by rw [k2.gpr (by decide), h.rdi]; rfl, by rw [hcx, ← BitVec.ofNat_toNat, hn]; rfl,
    fun k hk => absurd hk (by simp [sampleAfter_zero])⟩

omit hp in
theorem zf_last {N t : Nat} (hN : N ≤ 280) (ht : t < N) :
    (BitVec.ofNat 64 (N - t) - 1 == 0) = decide (t + 1 = N) := by
  rw [ofNat64_pred (by omega) (by omega), ofNat64_beq_zero (by omega)]
  exact decide_eq_decide.mpr (by omega)

/-- `N` iterations of the loop. -/
theorem loop_ok {n : BitVec 32} {N : Nat} (hn : n.toNat = N) (hN0 : 0 < N) (hN : N ≤ 280) {s : State}
    (h : VG.Proof.MlKem.X86_64.SampleNtt.I6 σ (3 * N) s) : WP isa (snLoop n) s (VG.Proof.MlKem.X86_64.SampleNtt.LAt σ N N) := by
  unfold snLoop
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.SampleNtt.latA h) fun s1 h1 => WP.seq (WP.mono (VG.Proof.MlKem.X86_64.SampleNtt.latB hn h1) fun s2 h2 => ?_))
  refine WP.loop (M := isa) (fun m s => ∃ t, m = N - t ∧ t < N ∧ VG.Proof.MlKem.X86_64.SampleNtt.LAt σ N t s) ?_ N s2 ⟨0, by omega, hN0, h2⟩
  rintro m s ⟨t, rfl, ht, hI⟩
  refine WP.mono (VG.Proof.MlKem.X86_64.SampleNtt.lat_step hp hN ht hI) fun s' ⟨hI', hz'⟩ => ?_
  have he : isa.eval .ne s' = some (!decide (t + 1 = N)) := by
    show s'.zf.map (!·) = _
    rw [hz', VG.Proof.MlKem.X86_64.SampleNtt.zf_last hN ht]; rfl
  by_cases hl : t + 1 = N
  · exact .inl ⟨by rw [he, decide_eq_true hl]; rfl, by subst hl; exact hI'⟩
  · exact .inr ⟨by rw [he, decide_eq_false hl]; rfl, _, by omega, t + 1, rfl, by omega, hI'⟩

/-- `snSample n`: the sponge, and `N` iterations of the loop. -/
theorem sample_ok {n : BitVec 32} {N : Nat} (hn : n.toNat = N) (h3 : (3 * n).toNat = 3 * N) (hN0 : 0 < N)
    (hN : N ≤ 280) {s : State} (h : VG.Proof.MlKem.X86_64.SampleNtt.I1 σ s) : WP isa (snSample n) s (VG.Proof.MlKem.X86_64.SampleNtt.LAt σ N N) := by
  unfold snSample
  exact WP.seq (WP.mono (VG.Proof.MlKem.X86_64.SampleNtt.callB_ok hp h) fun s2 h2 => WP.seq (WP.mono (VG.Proof.MlKem.X86_64.SampleNtt.blkC_ok hp h2) fun s3 h3' =>
    WP.seq (WP.mono (VG.Proof.MlKem.X86_64.SampleNtt.callD_ok hp h3') fun s4 h4 => WP.seq (WP.mono (VG.Proof.MlKem.X86_64.SampleNtt.blkE_ok hp h3 (by omega) h4) fun s5 h5 =>
      WP.seq (WP.mono (VG.Proof.MlKem.X86_64.SampleNtt.callF_ok hp (by omega) h5) fun s6 h6 => VG.Proof.MlKem.X86_64.SampleNtt.loop_ok hp hn hN0 hN h6)))))

/-! ## The second run and the end -/

/-- The coefficients sampled. -/
abbrev Ls (σ : State) : List Zq := VG.Proof.MlKem.X86_64.SampleNtt.Lt σ 280

/-- The end: the postcondition and the calling convention. -/
def Fin (σ s : State) : Prop := sampleK.post σ s ∧ gprPreserved σ s

/-- After the loops. -/
structure IEnd (σ s : State) : Prop where
  env : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s
  rdi : s.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlKem.X86_64.SampleNtt.Ls σ).length
  stored : VG.Proof.MlKem.X86_64.Stored s.mem (VG.Proof.MlKem.X86_64.SampleNtt.aP σ) (VG.Proof.MlKem.X86_64.SampleNtt.Ls σ)

omit hp in
/-- 168 iterations that sampled 256 coefficients sampled all of them. -/
theorem ls_full (hf : (VG.Proof.MlKem.X86_64.SampleNtt.Lt σ 168).length = 256) : VG.Proof.MlKem.X86_64.SampleNtt.Ls σ = VG.Proof.MlKem.X86_64.SampleNtt.Lt σ 168 :=
  sampleAfter_full (by rw [n_eq]; exact hf) 280 (by omega)

/-- `seed` in `rcx`, and `snAbs`. -/
theorem redo_ok {s : State} (he : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s) :
    WP isa (.block (.mov .rcx (.mem (at_ .rbx 1696)) :: snAbs)) s (VG.Proof.MlKem.X86_64.SampleNtt.I1 σ) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 1696) 8 := by
    rw [VG.Proof.MlKem.X86_64.SampleNtt.regions hp he, he.rbx]; exact ⟨VG.Proof.MlKem.X86_64.SampleNtt.scrR σ, by simp, contains_offset' (by omega) (by omega)⟩
  rw [show (.mov .rcx (.mem (at_ .rbx 1696)) :: snAbs : List Instr) = ([.mov .rcx (.mem (at_ .rbx 1696))] : List Instr) ++ snAbs
    from rfl, WP.block_append_iff]
  refine WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rcx = s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 1696) 64) (by xrun [hin]) (by decide))
    fun s1 ⟨⟨hm, hcx⟩, k⟩ => VG.Proof.MlKem.X86_64.SampleNtt.abs_ok hp (he.keep hm (k.mono (by decide))) ?_
  rw [hcx, he.rbx]; exact he.saved.2.2

/-- After the check of `j`. -/
structure IM (σ s : State) : Prop where
  env : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s
  rdi : s.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlKem.X86_64.SampleNtt.Lt σ 168).length
  stored : VG.Proof.MlKem.X86_64.Stored s.mem (VG.Proof.MlKem.X86_64.SampleNtt.aP σ) (VG.Proof.MlKem.X86_64.SampleNtt.Lt σ 168)
  cf : s.cf = some (decide ((VG.Proof.MlKem.X86_64.SampleNtt.Lt σ 168).length < 256))

omit hp in
theorem cmp_ok {s : State} (h : VG.Proof.MlKem.X86_64.SampleNtt.LAt σ 168 168 s) : WP isa (.block [.alu .cmp .rdi (.imm 256)]) s (VG.Proof.MlKem.X86_64.SampleNtt.IM σ) := by
  refine WP.mono (VG.Proof.MlKem.X86_64.cmpRdi_ok s) fun s1 ⟨hc, hm, hg, hrd, hwr⟩ => ?_
  have hL : (VG.Proof.MlKem.X86_64.SampleNtt.Lt σ 168).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ 168
  have hk : Keep [] s s1 := ⟨fun r _ => by rw [hg], hrd, hwr⟩
  rw [h.rdi, VG.Proof.MlKem.X86_64.ofNat64_toNat (by omega)] at hc
  exact ⟨h.env.keep hm (hk.mono (by simp)), by rw [hk.gpr (by simp), h.rdi], by rw [hm]; exact h.stored, hc⟩

/-- The 280 iterations, from the start. -/
theorem redo_all_ok {s : State} (he : VG.Proof.MlKem.X86_64.SampleNtt.Env σ s) :
    WP isa (.seq (.block (.mov .rcx (.mem (at_ .rbx 1696)) :: snAbs)) (snSample 280)) s (VG.Proof.MlKem.X86_64.SampleNtt.IEnd σ) :=
  WP.seq (WP.mono (VG.Proof.MlKem.X86_64.SampleNtt.redo_ok hp he) fun _ h2 =>
    WP.mono (VG.Proof.MlKem.X86_64.SampleNtt.sample_ok hp (n := 280) (N := 280) (by decide) (by decide) (by omega) (by omega) h2) fun _ h3 =>
      ⟨h3.env, h3.rdi, h3.stored⟩)

omit hp in
/-- Without them, if `j = 256`. -/
theorem skip_ok {s : State} (h : VG.Proof.MlKem.X86_64.SampleNtt.IM σ s) (hb : s.cf = some false) : VG.Proof.MlKem.X86_64.SampleNtt.IEnd σ s := by
  have hL : (VG.Proof.MlKem.X86_64.SampleNtt.Lt σ 168).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ 168
  have hf : (VG.Proof.MlKem.X86_64.SampleNtt.Lt σ 168).length = 256 := by
    rw [h.cf, Option.some.injEq, decide_eq_false_iff_not] at hb; omega
  exact ⟨h.env, by rw [h.rdi, VG.Proof.MlKem.X86_64.SampleNtt.ls_full hf], by rw [VG.Proof.MlKem.X86_64.SampleNtt.ls_full hf]; exact h.stored⟩

/-- The check of `j`, and the 280 iterations if it is less than 256. -/
theorem more_ok {s : State} (h : VG.Proof.MlKem.X86_64.SampleNtt.LAt σ 168 168 s) : WP isa snMore s (VG.Proof.MlKem.X86_64.SampleNtt.IEnd σ) := by
  unfold snMore
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.SampleNtt.cmp_ok h) fun s1 h1 => ?_)
  exact WP.ite _ h1.cf (fun _ => VG.Proof.MlKem.X86_64.SampleNtt.redo_all_ok hp h1.env) fun hb => WP.block_nil (VG.Proof.MlKem.X86_64.SampleNtt.skip_ok h1 (by rw [h1.cf, hb]))

omit hp in
theorem ret_below (sp : Addr) : Region.Disjoint ⟨sp, 8⟩ (below sp 16) := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

omit hp in
theorem epi_ok (s : State) (h8 : InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 1688) 8)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 1680) 8) :
    WP isa (.block snEpi) s fun s' =>
      (s'.gpr .rax = s.gpr .rdi >>> 8 ∧ s'.gpr .rbp = s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 1688) 64 ∧
        s'.gpr .rbx = s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 1680) 64 ∧ s'.mem = s.mem) ∧
      Keep [.rax, .rbp, .rbx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold snEpi
  xrun [h8, h0]

omit hp in
theorem stored_polyAt {m : Mem} {aP : Addr} {L : List Zq} (h : VG.Proof.MlKem.X86_64.Stored m aP L) (hL : L.length = 256) :
    Reduced m aP ∧ polyAt m aP = toPoly L := by
  have hv : ∀ i < 256, (coeffAt m aP i).toNat = (L.getD i 0).val := fun i hi => by
    rw [h i (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := val_lt (L.getD i 0); omega)]
  refine ⟨fun i hi => by rw [hv i hi]; exact val_lt _, ?_⟩
  apply Vector.ext
  intro i hi
  simp only [polyAt, toPoly, Vector.getElem_ofFn, hv i hi, ofNat_val]

theorem end_ok {s : State} (h : VG.Proof.MlKem.X86_64.SampleNtt.IEnd σ s) : WP isa (.block snEpi) s (VG.Proof.MlKem.X86_64.SampleNtt.Fin σ) := by
  have hbx2 : s.gpr .rbx = VG.Proof.MlKem.X86_64.SampleNtt.scr σ := h.env.rbx
  have hrr2 := VG.Proof.MlKem.X86_64.SampleNtt.regions hp h.env
  have hsv := h.env.saved
  refine WP.mono (VG.Proof.MlKem.X86_64.SampleNtt.epi_ok s (by rw [hrr2, hbx2]; exact ⟨VG.Proof.MlKem.X86_64.SampleNtt.scrR σ, by simp, contains_offset' (by omega) (by omega)⟩)
    (by rw [hrr2, hbx2]; exact ⟨VG.Proof.MlKem.X86_64.SampleNtt.scrR σ, by simp, contains_offset' (by omega) (by omega)⟩))
    fun s3 ⟨⟨hax, hbp, hbx, hm3⟩, k3⟩ => ?_
  rw [hbx2] at hbp hbx
  have hL : (VG.Proof.MlKem.X86_64.SampleNtt.Ls σ).length ≤ 256 := sampleAfter_length_le (a := []) (by simp) _ 280
  have hr : (s3.gpr .rax).setWidth 32 = BitVec.ofNat 32 ((VG.Proof.MlKem.X86_64.SampleNtt.Ls σ).length / 256) := by
    apply BitVec.eq_of_toNat_eq
    rw [hax, h.rdi, BitVec.toNat_setWidth, shr_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := (VG.Proof.MlKem.X86_64.SampleNtt.Ls σ).length) (by omega)]
  have hfr : Frame [pR (VG.Proof.MlKem.X86_64.SampleNtt.aP σ), VG.Proof.MlKem.X86_64.SampleNtt.scrR σ, below (σ.gpr .rsp) 16] σ.mem s3.mem := by
    rw [hm3]; exact h.env.frame
  refine ⟨?_, fun r hr' => ?_, ?_⟩
  · by_cases hfull : (VG.Proof.MlKem.X86_64.SampleNtt.Ls σ).length = 256
    · have e1 : (s3.gpr .rax).setWidth 32 = 1 := by rw [hr, hfull]; rfl
      obtain ⟨hred, hpoly⟩ := VG.Proof.MlKem.X86_64.SampleNtt.stored_polyAt (m := s3.mem) (aP := VG.Proof.MlKem.X86_64.SampleNtt.aP σ) (by rw [hm3]; exact h.stored) hfull
      have hs : sampleNTT minIterations (VG.Proof.MlKem.X86_64.SampleNtt.B σ) = some (toPoly (VG.Proof.MlKem.X86_64.SampleNtt.Ls σ)) :=
        sampleNTT_of_full (Nat.le_refl _) (by rw [n_eq]; exact hfull)
      refine ⟨by rw [e1, hs]; rfl, fun f hf => ?_⟩
      rw [hs] at hf
      rw [← Option.some.inj hf]
      exact ⟨hred, hpoly⟩
    · have e0 : (s3.gpr .rax).setWidth 32 = 0 := by rw [hr, Nat.div_eq_of_lt (by omega)]; rfl
      have hs : sampleNTT minIterations (VG.Proof.MlKem.X86_64.SampleNtt.B σ) = none := sampleNTT_none (by rw [n_eq]; exact hfull)
      refine ⟨by rw [e0, hs]; rfl, fun f hf => ?_⟩
      rw [hs] at hf
      exact absurd hf (Option.some_ne_none f).symm
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hbx.trans hsv.1
    · exact hbp.trans hsv.2.1
    all_goals rw [k3.gpr (by decide)]
    · exact h.env.rsp
    all_goals exact h.env.cs _ (by decide)
  · exact hfr.readW (Region.contains_self _ _) (by
      simpa using ⟨hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1, VG.Proof.MlKem.X86_64.SampleNtt.ret_below _⟩) (by decide)

end

end SampleNtt

theorem sample_correct (σ : State) (hp : sampleK.pre σ) :
    ∃ t s', Exec isa Impl.MlKem.X86_64.sampleNTT σ t s' ∧ abiPreserved σ s' ∧ sampleK.post σ s' := by
  open SampleNtt in
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (VG.Proof.MlKem.X86_64.SampleNtt.proA_ok hp) fun s1 h1 =>
    WP.seq (WP.mono (VG.Proof.MlKem.X86_64.SampleNtt.sample_ok hp (n := 168) (N := 168) (by decide) (by decide) (by omega) (by omega) h1) fun s2 h2 =>
      WP.seq (WP.mono (VG.Proof.MlKem.X86_64.SampleNtt.more_ok hp h2) fun s3 h3 => VG.Proof.MlKem.X86_64.SampleNtt.end_ok hp h3)))
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hF.2, hF.1⟩

end VG.Proof.MlKem.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86_64.SampleCT`. -/
section

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt`, constant time but for the seed

Two runs whose seeds (the declared leak) and pointers agree leak the same: the
prologue and the arguments of the calls are proven by the taint analysis, the
calls by the sponge functions' own proofs (`RelCT.callEx`), and the loop,
whose branches and stores depend on the XOF output, by relating the two runs
iteration by iteration (`body_ct`): both are at the same iteration with the
same coefficients sampled and the same bytes to read, so each branch goes the
same way and each store goes to the same address.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)

/-- What holds of every run of `c` from `s` that `Q a` does, for any `a`
with `Pre a` (by determinism). -/
theorem WP.all {c : Prog isa} {s : State} {α : Sort _} {Pre : α → Prop} {Q : α → State → Prop}
    (h : ∀ a, Pre a → WP isa c s (Q a)) (hne : ∃ a, Pre a) : WP isa c s fun s' => ∀ a, Pre a → Q a s' := by
  obtain ⟨a₀, h₀⟩ := hne
  obtain ⟨t, s', e, -⟩ := h a₀ h₀
  refine ⟨t, s', e, fun a ha => ?_⟩
  obtain ⟨t', s'', e', q⟩ := h a ha
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact q

/-! ## A try -/

theorem traceTry (r : Reg) {h : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.rbp, .rdi]) (.block (snTry r)) h).isSome = true) :
    RelCT isa (fun s₁ s₂ => s₁.gpr .rbp = s₂.gpr .rbp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧
      (s₁.gpr r).setWidth 32 = (s₂.gpr r).setWidth 32) (.block (snTry r)) fun _ _ => True :=
  VG.Proof.MlKem.X86_64.taintRel [.rbp, .rdi] (fun x y h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.1, h.2.1]) c

/-- The hypotheses of `snTry_ok`. -/
structure TryPre (s : State) (aP : Addr) (L : List Zq) : Prop where
  rbp : s.gpr .rbp = aP
  rdi : s.gpr .rdi = BitVec.ofNat 64 L.length
  len : L.length < 256
  wr : VG.Proof.MlKem.X86_64.WrA s.wr aP
  st : VG.Proof.MlKem.X86_64.Stored s.mem aP L

/-- The coefficients after a try of the value in `r`. -/
def tryL (L : List Zq) (d : Nat) : List Zq := if d < q then L ++ [ofNat d] else L

theorem tryL_len (L : List Zq) (d : Nat) : (VG.Proof.MlKem.X86_64.tryL L d).length ≤ L.length + 1 := by
  unfold VG.Proof.MlKem.X86_64.tryL; split <;> simp

theorem snTry_all (r : Reg) (s : State) (hne : ∃ aP L, VG.Proof.MlKem.X86_64.TryPre s aP L) :
    WP isa (.block (snTry r)) s fun s' => ∀ aP L, VG.Proof.MlKem.X86_64.TryPre s aP L →
      s'.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlKem.X86_64.tryL L ((s.gpr r).setWidth 32).toNat).length ∧
      VG.Proof.MlKem.X86_64.Stored s'.mem aP (VG.Proof.MlKem.X86_64.tryL L ((s.gpr r).setWidth 32).toNat) ∧ Frame [pR aP] s.mem s'.mem ∧
        Keep [.rdi, r] s s' := by
  have := WP.all (Pre := fun p : Addr × List Zq => VG.Proof.MlKem.X86_64.TryPre s p.1 p.2)
    (Q := fun p s' => s'.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlKem.X86_64.tryL p.2 ((s.gpr r).setWidth 32).toNat).length ∧
      VG.Proof.MlKem.X86_64.Stored s'.mem p.1 (VG.Proof.MlKem.X86_64.tryL p.2 ((s.gpr r).setWidth 32).toNat) ∧ Frame [pR p.1] s.mem s'.mem ∧
        Keep [.rdi, r] s s')
    (fun p h => VG.Proof.MlKem.X86_64.snTry_ok r s h.rbp h.rdi h.len h.wr h.st) (by obtain ⟨aP, L, h⟩ := hne; exact ⟨(aP, L), h⟩)
  exact WP.mono this fun s' h aP L hp => h (aP, L) hp

/-! ## The middle of an iteration -/

/-- The hypotheses of `snMid_ok`. -/
structure MPre (s : State) (aP : Addr) (L : List Zq) : Prop where
  rbp : s.gpr .rbp = aP
  rdi : s.gpr .rdi = BitVec.ofNat 64 L.length
  len : L.length ≤ 256
  wr : VG.Proof.MlKem.X86_64.WrA s.wr aP
  st : VG.Proof.MlKem.X86_64.Stored s.mem aP L
  cf : s.cf = some (decide ((s.gpr .rdi).toNat < 256))

/-- After the loads. -/
def R1 (s₁ s₂ : State) : Prop :=
  ∃ aP L, VG.Proof.MlKem.X86_64.MPre s₁ aP L ∧ VG.Proof.MlKem.X86_64.MPre s₂ aP L ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .rcx = s₂.gpr .rcx

/-- After the first try. -/
structure P3 (s : State) (aP : Addr) (L : List Zq) : Prop where
  rbp : s.gpr .rbp = aP
  rdi : s.gpr .rdi = BitVec.ofNat 64 L.length
  len : L.length ≤ 256
  wr : VG.Proof.MlKem.X86_64.WrA s.wr aP
  st : VG.Proof.MlKem.X86_64.Stored s.mem aP L

def R3 (s₁ s₂ : State) : Prop :=
  ∃ aP L, VG.Proof.MlKem.X86_64.P3 s₁ aP L ∧ VG.Proof.MlKem.X86_64.P3 s₂ aP L ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rcx = s₂.gpr .rcx

/-- After the comparison of `j` with 256. -/
def R4 (s₁ s₂ : State) : Prop :=
  ∃ aP L, VG.Proof.MlKem.X86_64.P3 s₁ aP L ∧ VG.Proof.MlKem.X86_64.P3 s₂ aP L ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.cf = some (decide (L.length < 256)) ∧ s₂.cf = some (decide (L.length < 256))

theorem ofNat64_toNat' {j : Nat} (h : j ≤ 256) : (BitVec.ofNat 64 j).toNat = j := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem tailTry_ct : RelCT isa VG.Proof.MlKem.X86_64.R4 (.ite .b (.block (snTry .r8)) (.block [])) fun s₁ s₂ => s₁.gpr .rcx = s₂.gpr .rcx := by
  refine RelCT.ite (fun x y ⟨aP, L, _, _, _, _, c1, c2⟩ => by show x.cf = y.cf; rw [c1, c2]) ?_ ?_
  · refine RelCT.postDep (F := fun (x x' : State) => ∀ aP L, VG.Proof.MlKem.X86_64.TryPre x aP L →
        x'.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlKem.X86_64.tryL L ((x.gpr .r8).setWidth 32).toNat).length ∧
        VG.Proof.MlKem.X86_64.Stored x'.mem aP (VG.Proof.MlKem.X86_64.tryL L ((x.gpr .r8).setWidth 32).toNat) ∧ Frame [pR aP] x.mem x'.mem ∧
          Keep [.rdi, .r8] x x')
      (RelCT.mono (VG.Proof.MlKem.X86_64.traceTry .r8 (by taint_decide)) (fun x y h => by
        obtain ⟨⟨aP, L, p1, p2, e8, _, _, _⟩, _⟩ := h
        exact ⟨by rw [p1.rbp, p2.rbp], by rw [p1.rdi, p2.rdi], by rw [e8]⟩) fun _ _ h => h) ?_ ?_
    · intro x y ⟨⟨aP, L, p1, p2, _, _, c1, _⟩, hb⟩
      have hl : L.length < 256 := by
        have : x.cf = some true := hb
        rw [c1] at this; simpa using this
      exact ⟨VG.Proof.MlKem.X86_64.snTry_all .r8 x ⟨aP, L, p1.rbp, p1.rdi, hl, p1.wr, p1.st⟩,
        VG.Proof.MlKem.X86_64.snTry_all .r8 y ⟨aP, L, p2.rbp, p2.rdi, hl, p2.wr, p2.st⟩⟩
    · intro x y x' y' ⟨⟨aP, L, p1, p2, _, ecx, c1, _⟩, hb⟩ f1 f2
      have hl : L.length < 256 := by
        have : x.cf = some true := hb
        rw [c1] at this; simpa using this
      rw [(f1 aP L ⟨p1.rbp, p1.rdi, hl, p1.wr, p1.st⟩).2.2.2.gpr (by decide),
        (f2 aP L ⟨p2.rbp, p2.rdi, hl, p2.wr, p2.st⟩).2.2.2.gpr (by decide), ecx]
  · refine RelCT.postDep (F := fun (x x' : State) => x' = x) (VG.Proof.MlKem.X86_64.taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil)
      (by taint_decide)) (fun x y _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) ?_
    intro x y x' y' ⟨⟨_, _, _, _, _, ecx, _, _⟩, _⟩ f1 f2
    rw [f1, f2]; exact ecx

theorem cmp256_ct : RelCT isa VG.Proof.MlKem.X86_64.R3 (.block [.alu .cmp .rdi (.imm 256)]) VG.Proof.MlKem.X86_64.R4 :=
  RelCT.postDep (F := fun (x x' : State) => x'.cf = some (decide ((x.gpr .rdi).toNat < 256)) ∧ x'.mem = x.mem ∧
      x'.gpr = x.gpr ∧ x'.rd = x.rd ∧ x'.wr = x.wr)
    (VG.Proof.MlKem.X86_64.taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide))
    (fun x y _ => ⟨VG.Proof.MlKem.X86_64.cmpRdi_ok x, VG.Proof.MlKem.X86_64.cmpRdi_ok y⟩) fun x y x' y' ⟨aP, L, p1, p2, e8, ecx⟩ f1 f2 => by
      have ep : ∀ {s s' : State}, VG.Proof.MlKem.X86_64.P3 s aP L → (s'.cf = some (decide ((s.gpr .rdi).toNat < 256)) ∧ s'.mem = s.mem ∧
          s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr) → VG.Proof.MlKem.X86_64.P3 s' aP L ∧ s'.cf = some (decide (L.length < 256)) :=
        fun {s s'} p ⟨c, m, g, _, w⟩ => ⟨⟨by rw [g, p.rbp], by rw [g, p.rdi], p.len, by rw [w]; exact p.wr,
          by rw [m]; exact p.st⟩, by rw [c, p.rdi, VG.Proof.MlKem.X86_64.ofNat64_toNat' p.len]⟩
      obtain ⟨q1, c1⟩ := ep p1 f1
      obtain ⟨q2, c2⟩ := ep p2 f2
      exact ⟨aP, L, q1, q2, by rw [f1.2.2.1, f2.2.2.1, e8], by rw [f1.2.2.1, f2.2.2.1, ecx], c1, c2⟩

theorem mid_ct : RelCT isa VG.Proof.MlKem.X86_64.R1
    (.ite .b (.seq (.block (snTry .r9)) (.seq (.block [.alu .cmp .rdi (.imm 256)]) (.ite .b (.block (snTry .r8)) (.block []))))
      (.block [])) fun s₁ s₂ => s₁.gpr .rcx = s₂.gpr .rcx := by
  refine RelCT.ite (fun x y ⟨aP, L, p1, p2, _⟩ => by
      show x.cf = y.cf; rw [p1.cf, p2.cf, p1.rdi, p2.rdi]) ?_ ?_
  · refine RelCT.seq (R := VG.Proof.MlKem.X86_64.R3) ?_ (RelCT.seq VG.Proof.MlKem.X86_64.cmp256_ct VG.Proof.MlKem.X86_64.tailTry_ct)
    refine RelCT.postDep (F := fun (x x' : State) => ∀ aP L, VG.Proof.MlKem.X86_64.TryPre x aP L →
        x'.gpr .rdi = BitVec.ofNat 64 (VG.Proof.MlKem.X86_64.tryL L ((x.gpr .r9).setWidth 32).toNat).length ∧
        VG.Proof.MlKem.X86_64.Stored x'.mem aP (VG.Proof.MlKem.X86_64.tryL L ((x.gpr .r9).setWidth 32).toNat) ∧ Frame [pR aP] x.mem x'.mem ∧
          Keep [.rdi, .r9] x x')
      (RelCT.mono (VG.Proof.MlKem.X86_64.traceTry .r9 (by taint_decide)) (fun x y h => by
        obtain ⟨⟨aP, L, p1, p2, e9, _, _⟩, _⟩ := h
        exact ⟨by rw [p1.rbp, p2.rbp], by rw [p1.rdi, p2.rdi], by rw [e9]⟩) fun _ _ h => h) ?_ ?_
    · intro x y ⟨⟨aP, L, p1, p2, _⟩, hb⟩
      have hl : L.length < 256 := by
        have : x.cf = some true := hb
        rw [p1.cf, p1.rdi, VG.Proof.MlKem.X86_64.ofNat64_toNat' p1.len] at this; simpa using this
      exact ⟨VG.Proof.MlKem.X86_64.snTry_all .r9 x ⟨aP, L, p1.rbp, p1.rdi, hl, p1.wr, p1.st⟩,
        VG.Proof.MlKem.X86_64.snTry_all .r9 y ⟨aP, L, p2.rbp, p2.rdi, hl, p2.wr, p2.st⟩⟩
    · intro x y x' y' ⟨⟨aP, L, p1, p2, e9, e8, ecx⟩, hb⟩ f1 f2
      have hl : L.length < 256 := by
        have : x.cf = some true := hb
        rw [p1.cf, p1.rdi, VG.Proof.MlKem.X86_64.ofNat64_toNat' p1.len] at this; simpa using this
      obtain ⟨d1, s1, _, k1⟩ := f1 aP L ⟨p1.rbp, p1.rdi, hl, p1.wr, p1.st⟩
      obtain ⟨d2, s2, _, k2⟩ := f2 aP L ⟨p2.rbp, p2.rdi, hl, p2.wr, p2.st⟩
      rw [e9] at d1 s1
      have hl' := VG.Proof.MlKem.X86_64.tryL_len L ((y.gpr .r9).setWidth 32).toNat
      exact ⟨aP, _, ⟨by rw [k1.gpr (by decide), p1.rbp], d1, by omega, by rw [k1.2.2]; exact p1.wr, s1⟩,
        ⟨by rw [k2.gpr (by decide), p2.rbp], d2, by omega, by rw [k2.2.2]; exact p2.wr, s2⟩,
        by rw [k1.gpr (by decide), k2.gpr (by decide), e8], by rw [k1.gpr (by decide), k2.gpr (by decide), ecx]⟩
  · refine RelCT.postDep (F := fun (x x' : State) => x' = x) (VG.Proof.MlKem.X86_64.taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil)
      (by taint_decide)) (fun x y _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) ?_
    intro x y x' y' ⟨⟨_, _, _, _, _, _, ecx⟩, _⟩ f1 f2
    rw [f1, f2]; exact ecx


/-! ## An iteration -/

/-- The hypotheses of `snBody_ok`. -/
structure BPre (s : State) (aP : Addr) (L : List Zq) : Prop where
  rbp : s.gpr .rbp = aP
  rdi : s.gpr .rdi = BitVec.ofNat 64 L.length
  len : L.length ≤ 256
  wr : VG.Proof.MlKem.X86_64.WrA s.wr aP
  st : VG.Proof.MlKem.X86_64.Stored s.mem aP L
  r0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1
  r1 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 1) 1
  r2 : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 2) 1

/-- Two runs at the start of an iteration, with the same coefficients sampled
and the same bytes to read. -/
def BRel (s₁ s₂ : State) : Prop :=
  ∃ aP L, VG.Proof.MlKem.X86_64.BPre s₁ aP L ∧ VG.Proof.MlKem.X86_64.BPre s₂ aP L ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    ∀ k < 3, s₁.mem (s₁.gpr .rsi + BitVec.ofNat 64 k) = s₂.mem (s₂.gpr .rsi + BitVec.ofNat 64 k)

theorem load_ct : RelCT isa VG.Proof.MlKem.X86_64.BRel (.block snLoad) VG.Proof.MlKem.X86_64.R1 := by
  refine RelCT.postDep (F := fun (x x' : State) =>
      (x'.gpr .r9 = BitVec.setWidth 64 (VG.Proof.MlKem.X86_64.d1w (x.mem (x.gpr .rsi)) (x.mem (x.gpr .rsi + BitVec.ofNat 64 1))) ∧
        x'.gpr .r8 = BitVec.setWidth 64 (VG.Proof.MlKem.X86_64.d2w (x.mem (x.gpr .rsi + BitVec.ofNat 64 1))
          (x.mem (x.gpr .rsi + BitVec.ofNat 64 2))) ∧
        x'.cf = some (decide ((x.gpr .rdi).toNat < 256)) ∧ x'.mem = x.mem ∧ x'.gpr .rdi = x.gpr .rdi) ∧
      Keep [.rax, .rdx, .r8, .r9, .rdi] x x')
    (VG.Proof.MlKem.X86_64.taintRel [.rsi] (fun x y ⟨_, _, _, _, esi, _⟩ r hr => by simp at hr; subst hr; exact esi) (by taint_decide))
    (fun x y ⟨_, _, p1, p2, _⟩ => ⟨VG.Proof.MlKem.X86_64.snLoad_ok x p1.r0 p1.r1 p1.r2, VG.Proof.MlKem.X86_64.snLoad_ok y p2.r0 p2.r1 p2.r2⟩) ?_
  intro x y x' y' ⟨aP, L, p1, p2, esi, ecx, eb⟩ ⟨⟨h9, h8, hc, hm, hdi⟩, k⟩ ⟨⟨h9', h8', hc', hm', hdi'⟩, k'⟩
  have e0 := eb 0 (by decide)
  rw [add_ofNat_zero, add_ofNat_zero] at e0
  have mp : ∀ {s s' : State}, VG.Proof.MlKem.X86_64.BPre s aP L → s'.cf = some (decide ((s.gpr .rdi).toNat < 256)) →
      s'.mem = s.mem → s'.gpr .rdi = s.gpr .rdi → Keep [.rax, .rdx, .r8, .r9, .rdi] s s' → VG.Proof.MlKem.X86_64.MPre s' aP L :=
    fun {s s'} p c m d kk => ⟨by rw [kk.gpr (by decide), p.rbp], by rw [d, p.rdi], p.len, by rw [kk.2.2]; exact p.wr,
      by rw [m]; exact p.st, by rw [c, d]⟩
  exact ⟨aP, L, mp p1 hc hm hdi k, mp p2 hc' hm' hdi' k', by rw [h9, h9', e0, eb 1 (by decide)],
    by rw [h8, h8', eb 1 (by decide), eb 2 (by decide)], by rw [k.gpr (by decide), k'.gpr (by decide), ecx]⟩

theorem step_ct : RelCT isa (fun s₁ s₂ => s₁.gpr .rcx = s₂.gpr .rcx)
    (.block [.alu .add .rsi (.imm 3), .alu .sub .rcx (.imm 1)]) fun s₁ s₂ => s₁.zf = s₂.zf :=
  RelCT.postDep (F := fun (x x' : State) => x'.zf = some (x.gpr .rcx - 1 == 0))
    (VG.Proof.MlKem.X86_64.taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide))
    (fun x y _ => ⟨WP.mono (VG.Proof.MlKem.X86_64.snStep_ok x) fun _ h => h.1.2.2.1, WP.mono (VG.Proof.MlKem.X86_64.snStep_ok y) fun _ h => h.1.2.2.1⟩)
    fun x y x' y' e f1 f2 => by rw [f1, f2, e]

theorem body_ct : RelCT isa VG.Proof.MlKem.X86_64.BRel snBody fun s₁ s₂ => s₁.zf = s₂.zf :=
  RelCT.seq VG.Proof.MlKem.X86_64.load_ct (RelCT.seq VG.Proof.MlKem.X86_64.mid_ct VG.Proof.MlKem.X86_64.step_ct)


/-! ## The whole function -/

namespace SampleNtt

section
variable {σ₁ σ₂ : State} (hq : sampleK.pub σ₁ σ₂)
include hq

theorem pub_B : VG.Proof.MlKem.X86_64.SampleNtt.B σ₁ = VG.Proof.MlKem.X86_64.SampleNtt.B σ₂ := hq.2.2.2.2
theorem pub_scr : VG.Proof.MlKem.X86_64.SampleNtt.scr σ₁ = VG.Proof.MlKem.X86_64.SampleNtt.scr σ₂ := hq.2.2.1
theorem pub_at (k : Nat) : VG.Proof.MlKem.X86_64.SampleNtt.at' σ₁ k = VG.Proof.MlKem.X86_64.SampleNtt.at' σ₂ k := by simp only [VG.Proof.MlKem.X86_64.SampleNtt.at', VG.Proof.MlKem.X86_64.SampleNtt.pub_scr hq]
theorem pub_aP : VG.Proof.MlKem.X86_64.SampleNtt.aP σ₁ = VG.Proof.MlKem.X86_64.SampleNtt.aP σ₂ := hq.2.1
theorem pub_sd : VG.Proof.MlKem.X86_64.SampleNtt.sd σ₁ = VG.Proof.MlKem.X86_64.SampleNtt.sd σ₂ := hq.1
theorem pub_Lt (t : Nat) : VG.Proof.MlKem.X86_64.SampleNtt.Lt σ₁ t = VG.Proof.MlKem.X86_64.SampleNtt.Lt σ₂ t := by simp only [VG.Proof.MlKem.X86_64.SampleNtt.Lt, VG.Proof.MlKem.X86_64.SampleNtt.pub_B hq]

end

/-- Two runs at iteration `t` of `N`, `n = N - t` iterations from the end. -/
def LI (N n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂ t, sampleK.pre σ₁ ∧ sampleK.pre σ₂ ∧ sampleK.pub σ₁ σ₂ ∧ n = N - t ∧ t < N ∧
    VG.Proof.MlKem.X86_64.SampleNtt.LAt σ₁ N t s₁ ∧ VG.Proof.MlKem.X86_64.SampleNtt.LAt σ₂ N t s₂

theorem bpre {σ : State} (hp : sampleK.pre σ) {N t : Nat} (hN : N ≤ 280) (ht : t < N) {s : State}
    (h : VG.Proof.MlKem.X86_64.SampleNtt.LAt σ N t s) : VG.Proof.MlKem.X86_64.BPre s (VG.Proof.MlKem.X86_64.SampleNtt.aP σ) (VG.Proof.MlKem.X86_64.SampleNtt.Lt σ t) :=
  ⟨h.env.rbp, h.rdi, sampleAfter_length_le (a := []) (by simp) _ t, WrA.of_mem (by rw [h.env.wr, hp.2.1]; simp), h.stored,
    by simpa using VG.Proof.MlKem.X86_64.SampleNtt.lat_regions hp hN h (k := 0) (by omega), VG.Proof.MlKem.X86_64.SampleNtt.lat_regions hp hN h (by omega),
    VG.Proof.MlKem.X86_64.SampleNtt.lat_regions hp hN h (by omega)⟩

theorem li_brel {N n : Nat} (hN : N ≤ 280) {s₁ s₂ : State} (h : VG.Proof.MlKem.X86_64.SampleNtt.LI N n s₁ s₂) : VG.Proof.MlKem.X86_64.BRel s₁ s₂ := by
  obtain ⟨σ₁, σ₂, t, p₁, p₂, hq, _, ht, l₁, l₂⟩ := h
  refine ⟨VG.Proof.MlKem.X86_64.SampleNtt.aP σ₁, VG.Proof.MlKem.X86_64.SampleNtt.Lt σ₁ t, VG.Proof.MlKem.X86_64.SampleNtt.bpre p₁ hN ht l₁, by rw [VG.Proof.MlKem.X86_64.SampleNtt.pub_aP hq, VG.Proof.MlKem.X86_64.SampleNtt.pub_Lt hq]; exact VG.Proof.MlKem.X86_64.SampleNtt.bpre p₂ hN ht l₂,
    by rw [l₁.rsi, l₂.rsi, VG.Proof.MlKem.X86_64.SampleNtt.pub_at hq], by rw [l₁.rcx, l₂.rcx], fun k hk => ?_⟩
  rw [VG.Proof.MlKem.X86_64.SampleNtt.out_byte l₁ (by omega), VG.Proof.MlKem.X86_64.SampleNtt.out_byte l₂ (by omega), VG.Proof.MlKem.X86_64.SampleNtt.pub_B hq]

theorem loop_ct {N : Nat} (hN : N ≤ 280) (n : Nat) :
    RelCT isa (VG.Proof.MlKem.X86_64.SampleNtt.LI N n) (.loop snBody .ne) (VG.Proof.MlKem.X86_64.Rel2 sampleK.pre sampleK.pub fun σ s => VG.Proof.MlKem.X86_64.SampleNtt.LAt σ N N s) := by
  refine RelCT.loop (M := isa) (VG.Proof.MlKem.X86_64.SampleNtt.LI N) (fun n => ?_) n
  refine RelCT.postDep (F := fun (x x' : State) => ∀ p : State × Nat, sampleK.pre p.1 ∧ p.2 < N ∧ VG.Proof.MlKem.X86_64.SampleNtt.LAt p.1 N p.2 x →
      VG.Proof.MlKem.X86_64.SampleNtt.LAt p.1 N (p.2 + 1) x' ∧ x'.zf = some (BitVec.ofNat 64 (N - p.2) - 1 == 0))
    (RelCT.mono VG.Proof.MlKem.X86_64.body_ct (fun x y h => VG.Proof.MlKem.X86_64.SampleNtt.li_brel hN h) fun _ _ _ => trivial) (fun x y h => ?_) ?_
  · obtain ⟨σ₁, σ₂, t, p₁, p₂, _, _, ht, l₁, l₂⟩ := h
    exact ⟨WP.all (fun p hp' => VG.Proof.MlKem.X86_64.SampleNtt.lat_step hp'.1 hN hp'.2.1 hp'.2.2) ⟨(σ₁, t), p₁, ht, l₁⟩,
      WP.all (fun p hp' => VG.Proof.MlKem.X86_64.SampleNtt.lat_step hp'.1 hN hp'.2.1 hp'.2.2) ⟨(σ₂, t), p₂, ht, l₂⟩⟩
  · intro x y x' y' ⟨σ₁, σ₂, t, p₁, p₂, hq, hn, ht, l₁, l₂⟩ f₁ f₂
    obtain ⟨l₁', z₁⟩ := f₁ (σ₁, t) ⟨p₁, ht, l₁⟩
    obtain ⟨l₂', z₂⟩ := f₂ (σ₂, t) ⟨p₂, ht, l₂⟩
    rw [VG.Proof.MlKem.X86_64.SampleNtt.zf_last hN ht] at z₁ z₂
    refine ⟨by show x'.zf.map _ = y'.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht' => ?_⟩
    · have : t + 1 = N := by
        have : x'.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [this] at l₁' l₂'
      exact ⟨σ₁, σ₂, p₁, p₂, hq, l₁', l₂'⟩
    · have : t + 1 ≠ N := by
        have : x'.zf.map (!·) = some true := ht'
        rw [z₁] at this; simpa using this
      exact ⟨N - (t + 1), by omega, σ₁, σ₂, t + 1, p₁, p₂, hq, rfl, by omega, l₁', l₂'⟩

theorem regs_pub {σ₁ σ₂ s₁ s₂ : State} (hq : sampleK.pub σ₁ σ₂) (e₁ : VG.Proof.MlKem.X86_64.SampleNtt.Env σ₁ s₁) (e₂ : VG.Proof.MlKem.X86_64.SampleNtt.Env σ₂ s₂) :
    s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .rsp = s₂.gpr .rsp := by
  rw [e₁.rbx, e₂.rbx, e₁.rsp, e₂.rsp, VG.Proof.MlKem.X86_64.SampleNtt.pub_scr hq]; exact ⟨rfl, hq.2.2.2.1⟩

/-- `N` iterations of the loop, given the taint analysis of setting the counter. -/
theorem snLoop_ct {n : BitVec 32} {N : Nat} (hn : n.toNat = N) (hN0 : 0 < N) (hN : N ≤ 280)
    {hc : VG.Taint.Hint X86_64.Taint.T}
    (cB : (taint.check (X86_64.Taint.ofRegs []) (.block [.mov32 .rcx (.imm n)]) hc).isSome = true) :
    RelCT isa (VG.Proof.MlKem.X86_64.Rel2 sampleK.pre sampleK.pub (fun σ s => VG.Proof.MlKem.X86_64.SampleNtt.I6 σ (3 * N) s)) (snLoop n)
      (VG.Proof.MlKem.X86_64.Rel2 sampleK.pre sampleK.pub fun σ s => VG.Proof.MlKem.X86_64.SampleNtt.LAt σ N N s) :=
  RelCT.seq (VG.Proof.MlKem.X86_64.relInv (I' := fun σ s => VG.Proof.MlKem.X86_64.SampleNtt.IA σ N s) (fun σ s _ h => VG.Proof.MlKem.X86_64.SampleNtt.latA h)
      (VG.Proof.MlKem.X86_64.taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide)))
    (RelCT.seq (RelCT.mono (VG.Proof.MlKem.X86_64.relInv (I' := fun σ s => VG.Proof.MlKem.X86_64.SampleNtt.LAt σ N 0 s) (fun σ s _ h => VG.Proof.MlKem.X86_64.SampleNtt.latB hn h)
        (VG.Proof.MlKem.X86_64.taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil) cB))
      (fun _ _ h => h) fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, l₁, l₂⟩ => ⟨σ₁, σ₂, 0, p₁, p₂, hq, rfl, hN0, l₁, l₂⟩)
      (VG.Proof.MlKem.X86_64.SampleNtt.loop_ct hN N))

theorem nil_regs {P : State → State → Prop} : ∀ x y, P x y → ∀ r ∈ ([] : List Reg), x.gpr r = y.gpr r :=
  fun _ _ _ _ h => absurd h List.not_mem_nil

theorem absorb_ct' : RelCT isa (VG.Proof.MlKem.X86_64.Rel2 sampleK.pre sampleK.pub VG.Proof.MlKem.X86_64.SampleNtt.I1)
    (.call "vg_keccak_absorb_scratch" Impl.Sha3.X86_64.Stream.absorb) (VG.Proof.MlKem.X86_64.Rel2 sampleK.pre sampleK.pub VG.Proof.MlKem.X86_64.SampleNtt.I2) :=
  VG.Proof.MlKem.X86_64.relInv (fun σ s hp h => VG.Proof.MlKem.X86_64.SampleNtt.callB_ok hp h) (RelCT.callEx Proof.Sha3.X86_64.Stream.Absorb.absorb_correct
    Proof.Sha3.X86_64.Stream.Absorb.absorb_ct fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => by
      refine ⟨_, _, _, _, VG.Proof.MlKem.X86_64.absorb_pre h₁.args, VG.Proof.MlKem.X86_64.absorb_pre h₂.args, ?_, (VG.Proof.MlKem.X86_64.SampleNtt.covA p₁ h₁.env).1, (VG.Proof.MlKem.X86_64.SampleNtt.covA p₁ h₁.env).2,
        (VG.Proof.MlKem.X86_64.SampleNtt.covA p₂ h₂.env).1, (VG.Proof.MlKem.X86_64.SampleNtt.covA p₂ h₂.env).2, (VG.Proof.MlKem.X86_64.SampleNtt.regs_pub hq h₁.env h₂.env).2⟩
      simp only [Proof.Sha3.absorbX86_64, State.withRegions_gpr, State.callEntry_rsp,
        VG.Proof.MlKem.X86_64.ce_gpr _ (by decide : Reg.rdi ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr _ (by decide : Reg.rsi ≠ .rsp),
        VG.Proof.MlKem.X86_64.ce_gpr _ (by decide : Reg.rdx ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr _ (by decide : Reg.rcx ≠ .rsp),
        VG.Proof.MlKem.X86_64.ce_gpr _ (by decide : Reg.r8 ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr _ (by decide : Reg.r9 ≠ .rsp), h₁.args.rdi, h₂.args.rdi,
        h₁.args.rsi, h₂.args.rsi, h₁.args.rdx, h₂.args.rdx, h₁.args.rcx, h₂.args.rcx, h₁.args.r8, h₂.args.r8,
        h₁.args.r9, h₂.args.r9, VG.Proof.MlKem.X86_64.SampleNtt.pub_scr hq, VG.Proof.MlKem.X86_64.SampleNtt.pub_at hq, VG.Proof.MlKem.X86_64.SampleNtt.pub_sd hq, (VG.Proof.MlKem.X86_64.SampleNtt.regs_pub hq h₁.env h₂.env).2, and_self])

theorem pad_ct' : RelCT isa (VG.Proof.MlKem.X86_64.Rel2 sampleK.pre sampleK.pub VG.Proof.MlKem.X86_64.SampleNtt.I3)
    (.call "vg_keccak_pad_scratch" Impl.Sha3.X86_64.Stream.pad) (VG.Proof.MlKem.X86_64.Rel2 sampleK.pre sampleK.pub VG.Proof.MlKem.X86_64.SampleNtt.I4) :=
  VG.Proof.MlKem.X86_64.relInv (fun σ s hp h => VG.Proof.MlKem.X86_64.SampleNtt.callD_ok hp h) (RelCT.callEx Proof.Sha3.X86_64.Stream.Pad.pad_correct
    Proof.Sha3.X86_64.Stream.Pad.pad_ct fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => by
      refine ⟨_, _, _, _, VG.Proof.MlKem.X86_64.pad_pre h₁.args, VG.Proof.MlKem.X86_64.pad_pre h₂.args, ?_, (VG.Proof.MlKem.X86_64.SampleNtt.covP p₁ h₁.env).1, (VG.Proof.MlKem.X86_64.SampleNtt.covP p₁ h₁.env).2,
        (VG.Proof.MlKem.X86_64.SampleNtt.covP p₂ h₂.env).1, (VG.Proof.MlKem.X86_64.SampleNtt.covP p₂ h₂.env).2, (VG.Proof.MlKem.X86_64.SampleNtt.regs_pub hq h₁.env h₂.env).2⟩
      simp only [Proof.Sha3.padX86_64, State.withRegions_gpr, State.callEntry_rsp,
        VG.Proof.MlKem.X86_64.ce_gpr _ (by decide : Reg.rdi ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr _ (by decide : Reg.rsi ≠ .rsp),
        VG.Proof.MlKem.X86_64.ce_gpr _ (by decide : Reg.rdx ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr _ (by decide : Reg.r8 ≠ .rsp), h₁.args.rdi, h₂.args.rdi,
        h₁.args.rsi, h₂.args.rsi, h₁.args.rdx, h₂.args.rdx, h₁.args.r8, h₂.args.r8, VG.Proof.MlKem.X86_64.SampleNtt.pub_scr hq, VG.Proof.MlKem.X86_64.SampleNtt.pub_at hq,
        (VG.Proof.MlKem.X86_64.SampleNtt.regs_pub hq h₁.env h₂.env).2, and_self])

theorem squeeze_ct' {len : Nat} (hl : len ≤ 840) : RelCT isa (VG.Proof.MlKem.X86_64.Rel2 sampleK.pre sampleK.pub fun σ s => VG.Proof.MlKem.X86_64.SampleNtt.I5 σ len s)
    (.call "vg_keccak_squeeze_scratch" Impl.Sha3.X86_64.Stream.squeeze) (VG.Proof.MlKem.X86_64.Rel2 sampleK.pre sampleK.pub fun σ s => VG.Proof.MlKem.X86_64.SampleNtt.I6 σ len s) :=
  VG.Proof.MlKem.X86_64.relInv (fun σ s hp h => VG.Proof.MlKem.X86_64.SampleNtt.callF_ok hp hl h) (RelCT.callEx Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct
    Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct fun s₁ s₂ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => by
      refine ⟨_, _, _, _, VG.Proof.MlKem.X86_64.squeeze_pre h₁.args, VG.Proof.MlKem.X86_64.squeeze_pre h₂.args, ?_, (VG.Proof.MlKem.X86_64.SampleNtt.covS p₁ h₁.env hl).1,
        (VG.Proof.MlKem.X86_64.SampleNtt.covS p₁ h₁.env hl).2, (VG.Proof.MlKem.X86_64.SampleNtt.covS p₂ h₂.env hl).1, (VG.Proof.MlKem.X86_64.SampleNtt.covS p₂ h₂.env hl).2, (VG.Proof.MlKem.X86_64.SampleNtt.regs_pub hq h₁.env h₂.env).2⟩
      simp only [Proof.Sha3.squeezeX86_64, State.withRegions_gpr, State.callEntry_rsp,
        VG.Proof.MlKem.X86_64.ce_gpr _ (by decide : Reg.rdi ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr _ (by decide : Reg.rsi ≠ .rsp),
        VG.Proof.MlKem.X86_64.ce_gpr _ (by decide : Reg.rdx ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr _ (by decide : Reg.rcx ≠ .rsp),
        VG.Proof.MlKem.X86_64.ce_gpr _ (by decide : Reg.r8 ≠ .rsp), VG.Proof.MlKem.X86_64.ce_gpr _ (by decide : Reg.r9 ≠ .rsp), h₁.args.rdi, h₂.args.rdi,
        h₁.args.rsi, h₂.args.rsi, h₁.args.rdx, h₂.args.rdx, h₁.args.rcx, h₂.args.rcx, h₁.args.r8, h₂.args.r8,
        h₁.args.r9, h₂.args.r9, VG.Proof.MlKem.X86_64.SampleNtt.pub_scr hq, VG.Proof.MlKem.X86_64.SampleNtt.pub_at hq, (VG.Proof.MlKem.X86_64.SampleNtt.regs_pub hq h₁.env h₂.env).2, and_self])

/-- `snSample n`, given the taint analysis of the blocks with `n`. -/
theorem sample_ct' {n : BitVec 32} {N : Nat} (hn : n.toNat = N) (h3 : (3 * n).toNat = 3 * N) (hN0 : 0 < N)
    (hN : N ≤ 280) {hE hB : VG.Taint.Hint X86_64.Taint.T}
    (cE : (taint.check (X86_64.Taint.ofRegs []) (.block (snSqzArgs (3 * n))) hE).isSome = true)
    (cB : (taint.check (X86_64.Taint.ofRegs []) (.block [.mov32 .rcx (.imm n)]) hB).isSome = true) :
    RelCT isa (VG.Proof.MlKem.X86_64.Rel2 sampleK.pre sampleK.pub VG.Proof.MlKem.X86_64.SampleNtt.I1) (snSample n) (VG.Proof.MlKem.X86_64.Rel2 sampleK.pre sampleK.pub fun σ s => VG.Proof.MlKem.X86_64.SampleNtt.LAt σ N N s) :=
  RelCT.seq VG.Proof.MlKem.X86_64.SampleNtt.absorb_ct' (RelCT.seq (VG.Proof.MlKem.X86_64.relInv (I' := VG.Proof.MlKem.X86_64.SampleNtt.I3) (fun σ s hp h => VG.Proof.MlKem.X86_64.SampleNtt.blkC_ok hp h)
    (VG.Proof.MlKem.X86_64.taintRel [] VG.Proof.MlKem.X86_64.SampleNtt.nil_regs (by taint_decide))) (RelCT.seq VG.Proof.MlKem.X86_64.SampleNtt.pad_ct' (RelCT.seq
      (VG.Proof.MlKem.X86_64.relInv (I' := fun σ s => VG.Proof.MlKem.X86_64.SampleNtt.I5 σ (3 * N) s) (fun σ s hp h => VG.Proof.MlKem.X86_64.SampleNtt.blkE_ok hp h3 (by omega) h) (VG.Proof.MlKem.X86_64.taintRel [] VG.Proof.MlKem.X86_64.SampleNtt.nil_regs cE))
      (RelCT.seq (VG.Proof.MlKem.X86_64.SampleNtt.squeeze_ct' (by omega)) (VG.Proof.MlKem.X86_64.SampleNtt.snLoop_ct hn hN0 hN cB)))))

/-- The check of `j`, and the 280 iterations if it is less than 256: both
runs go the same way, since they sampled the same coefficients. -/
theorem more_ct : RelCT isa (VG.Proof.MlKem.X86_64.Rel2 sampleK.pre sampleK.pub fun σ s => VG.Proof.MlKem.X86_64.SampleNtt.LAt σ 168 168 s) snMore
    (VG.Proof.MlKem.X86_64.Rel2 sampleK.pre sampleK.pub VG.Proof.MlKem.X86_64.SampleNtt.IEnd) := by
  refine RelCT.seq (VG.Proof.MlKem.X86_64.relInv (I' := VG.Proof.MlKem.X86_64.SampleNtt.IM) (fun σ s _ h => VG.Proof.MlKem.X86_64.SampleNtt.cmp_ok h) (VG.Proof.MlKem.X86_64.taintRel [] VG.Proof.MlKem.X86_64.SampleNtt.nil_regs (by taint_decide))) ?_
  refine RelCT.ite (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ => by
    show x.cf = y.cf; rw [h₁.cf, h₂.cf, VG.Proof.MlKem.X86_64.SampleNtt.pub_Lt hq]) ?_ ?_
  · refine RelCT.mono (P := VG.Proof.MlKem.X86_64.Rel2 sampleK.pre sampleK.pub VG.Proof.MlKem.X86_64.SampleNtt.IM) (RelCT.seq (VG.Proof.MlKem.X86_64.relInv (I' := VG.Proof.MlKem.X86_64.SampleNtt.I1)
        (fun σ s hp h => VG.Proof.MlKem.X86_64.SampleNtt.redo_ok hp h.env) (VG.Proof.MlKem.X86_64.taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact (VG.Proof.MlKem.X86_64.SampleNtt.regs_pub hq h₁.env h₂.env).1) (by taint_decide)))
      (VG.Proof.MlKem.X86_64.SampleNtt.sample_ct' (n := 280) (N := 280) (by decide) (by decide) (by omega) (by omega) (by taint_decide)
        (by taint_decide))) (fun _ _ h => h.1) fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, l₁, l₂⟩ =>
      ⟨σ₁, σ₂, p₁, p₂, hq, ⟨l₁.env, l₁.rdi, l₁.stored⟩, ⟨l₂.env, l₂.rdi, l₂.stored⟩⟩
  · refine RelCT.mono (P := VG.Proof.MlKem.X86_64.Rel2 sampleK.pre sampleK.pub fun σ s => VG.Proof.MlKem.X86_64.SampleNtt.IM σ s ∧ s.cf = some false)
      (VG.Proof.MlKem.X86_64.relInv (I' := VG.Proof.MlKem.X86_64.SampleNtt.IEnd) (fun σ s _ h => WP.block_nil (VG.Proof.MlKem.X86_64.SampleNtt.skip_ok h.1 h.2)) (VG.Proof.MlKem.X86_64.taintRel [] VG.Proof.MlKem.X86_64.SampleNtt.nil_regs (by taint_decide)))
      (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩, hc⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, ⟨h₁, hc⟩, ⟨h₂, ?_⟩⟩) fun _ _ h => h
    have hc' : x.cf = some false := hc
    rw [h₂.cf, ← VG.Proof.MlKem.X86_64.SampleNtt.pub_Lt hq, ← h₁.cf, hc']

end SampleNtt

open SampleNtt in
theorem sample_ct : ConstantTime isa sampleK.pre sampleK.pub Impl.MlKem.X86_64.sampleNTT := by
  refine VG.Proof.MlKem.X86_64.relStart (Q := fun _ _ => True) (RelCT.seq (VG.Proof.MlKem.X86_64.relInv (I' := VG.Proof.MlKem.X86_64.SampleNtt.I1) (fun σ s hp h => by subst h; exact VG.Proof.MlKem.X86_64.SampleNtt.proA_ok hp)
    (VG.Proof.MlKem.X86_64.taintRel [.rdi, .rsi, .rdx, .rsp] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      subst h₁ h₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1]) (by taint_decide))) ?_)
  refine RelCT.seq (VG.Proof.MlKem.X86_64.SampleNtt.sample_ct' (n := 168) (N := 168) (by decide) (by decide) (by omega) (by omega) (by taint_decide)
    (by taint_decide)) (RelCT.seq VG.Proof.MlKem.X86_64.SampleNtt.more_ct ?_)
  exact VG.Proof.MlKem.X86_64.taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, l₁, l₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (VG.Proof.MlKem.X86_64.SampleNtt.regs_pub hq l₁.env l₂.env).1) (by taint_decide)

end VG.Proof.MlKem.X86_64

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

/-- A state satisfying the precondition. -/
def sampleSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 34⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem sample_verified :
    Verified X86_64.target Impl.MlKem.X86_64.sampleNTT (Spec.MlKem.sampleNTTContract X86_64.abi 16) :=
  Verified.of_correct VG.Proof.MlKem.X86_64.sample_correct VG.Proof.MlKem.X86_64.sample_ct
    { pre := by sig_implies_pre [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, VG.Proof.MlKem.X86_64.sampleK, X86_64.abi,
        X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, VG.Proof.MlKem.X86_64.sampleK, X86_64.abi, X86_64.argRegs]
        dsimp only [VG.Proof.MlKem.X86_64.sampleK] at h
        obtain ⟨hr, hp⟩ := h
        cases e : Spec.MlKem.sampleNTT Spec.MlKem.minIterations (Spec.Sha3.bytesAt s.mem (s.gpr .rdi) 34) with
        | none =>
          rw [e] at hr
          have h0 : BitVec.setWidth 32 (s'.gpr .rax) = 0 := hr
          exact ⟨fun h1 => absurd (h0.symm.trans h1) (by decide : (0 : BitVec 32) ≠ 1), .inr ⟨h0, e⟩⟩
        | some f =>
          rw [e] at hr
          have h1 : BitVec.setWidth 32 (s'.gpr .rax) = 1 := hr
          obtain ⟨hred, hf⟩ := hp f e
          exact ⟨fun _ => hred, .inl ⟨h1, Spec.MlKem.minIterations, by
            show Spec.MlKem.sampleNTT _ _ = _
            rw [e, hf]⟩⟩
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, VG.Proof.MlKem.X86_64.sampleK, X86_64.abi,
          X86_64.argRegs] at h
        obtain ⟨hsp, hb, hdi, hsi, hdx⟩ := h
        exact ⟨hdi, hsi, hdx, hsp, map_toNat_inj hb⟩
      sat := by sig_implies_sat [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, VG.Proof.MlKem.X86_64.sampleK, X86_64.abi,
        X86_64.argRegs] [sampleSat] using VG.Proof.MlKem.X86_64.sampleSat }

end VG.Proof.MlKem.X86_64

end
