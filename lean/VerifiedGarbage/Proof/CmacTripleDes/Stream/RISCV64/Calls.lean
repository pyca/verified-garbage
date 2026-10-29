module

public import VerifiedGarbage.Impl.CmacTripleDes.Stream.RISCV64
public import VerifiedGarbage.Proof.TripleDes.RISCV64.Key.Verified
public import VerifiedGarbage.Proof.TripleDes.RISCV64.EcbVerified
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Spec.Cmac
import VerifiedGarbage.Proof.TripleDes.RISCV64.FunctionsLit
import VerifiedGarbage.Proof.TripleDes.CbcBlocks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit

/-!
# Streaming TDEA-CMAC on RISC-V: the calls

The calls of the verified key expansion (`keyCall`, by `Key.contract`,
with `WP.call`: it uses no stack) and ECB encryption (`ecbCall`, by
`Ecb.ecbC`, with `WP.callAny`: it uses the 944 bytes below the stack
pointer, `ecb_sdepth`), as the streaming functions make them: the key
expansion writes the schedule at the start of the state `S`, and ECB
enciphers the block at `S + off` in place, a block of the state past the
schedule, with the state as the schedule. What each needs (`KArgs`,
`EArgs`), what it leaves (`KPost`, `EPost`, in terms of the memory before
the call), and that two calls with the same arguments leak the same
(`key_rel`, `ecb_rel`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64

theorem expandKey_noFrames : Impl.TripleDes.RISCV64.Key.expandKey.noFrames = true := by lit_decide

/-- ECB's frame uses the 944 bytes of stack its contract reserves. -/
theorem ecb_sdepth : sdepth (Impl.TripleDes.RISCV64.Ecb.ecb .encrypt) = 944 := by decide +kernel

theorem toNat_add_lt (p : Addr) {d k : Nat} (h : p.toNat + k ≤ 2 ^ 64) (hd : d < k) :
    (p + BitVec.ofNat 64 d).toNat = p.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64)]
  exact Nat.mod_eq_of_lt (by omega)

/-! ## The key expansion -/

/-- What the key expansion's call needs: the key at `K`, of `KL` bytes, and
the state at `S`. -/
structure KArgs (s : State) (K S : Addr) (KL : Nat) : Prop where
  a0 : s.gpr .a0 = K
  a1 : s.gpr .a1 = BitVec.ofNat 64 KL
  a2 : s.gpr .a2 = S
  valid : Spec.TripleDes.validKey KL
  ks : (⟨K, KL⟩ : Region).Disjoint ⟨S, 416⟩
  reads : (⟨K, KL⟩ : Region) ∈ s.rd
  writes : (⟨S, 416⟩ : Region) ∈ s.wr

/-- What the key expansion's call leaves. -/
structure KPost (s : State) (K S : Addr) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨S, 384⟩] s.mem s'.mem
  out : Spec.TripleDes.scheduleAt s'.mem S =
    Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem K KL)

theorem KArgs.toNat {s : State} {K S : Addr} {KL : Nat} (h : KArgs s K S KL) :
    (BitVec.ofNat 64 KL).toNat = KL := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by rcases h.valid with h | h <;> omega)

theorem KArgs.pre {s : State} {K S : Addr} {KL : Nat} (h : KArgs s K S KL) :
    Proof.TripleDes.RISCV64.Key.contract.pre (s.callEntry.withRegions [⟨K, KL⟩] [⟨S, 384⟩]) := by
  simp only [Proof.TripleDes.RISCV64.Key.contract, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.toNat]
  exact ⟨trivial, trivial, h.ks.sub_right (Region.sub_prefix (by decide)), h.valid⟩

theorem KArgs.covers {s : State} {K S : Addr} {KL : Nat} (h : KArgs s K S KL) :
    Covers ([⟨K, KL⟩] ++ [⟨S, 384⟩]) (s.rd ++ s.wr) ∧ Covers [⟨S, 384⟩] s.wr := by
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_append_left _ h.reads, 0, by simp, by simp⟩
    · exact ⟨_, List.mem_append_right _ h.writes, 0, by simp, by show 0 + 384 ≤ 416; decide⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨_, h.writes, 0, by simp, by show 0 + 384 ≤ 416; decide⟩

theorem key_call {s : State} {K S : Addr} {KL : Nat} (h : KArgs s K S KL) :
    WP isa Impl.CmacTripleDes.Stream.RISCV64.keyCall s (KPost s K S KL) := by
  refine WP.call (k := Proof.TripleDes.RISCV64.Key.contract)
    (Proof.TripleDes.RISCV64.Key.correct (by lit_decide) (by lit_decide)) h.pre h.covers.1 h.covers.2 ?_
    expandKey_noFrames
  intro s' hrd hwr hsp hf hsaved _ hpost
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [Proof.TripleDes.RISCV64.Key.contract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs),
    h.a0, h.a1, h.a2, h.toNat] at hpost
  exact hpost

theorem key_rel {K S : Addr} {KL : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → KArgs s₁ K S KL ∧ KArgs s₂ K S KL ∧ s₁.sp = s₂.sp) :
    RelCT isa P Impl.CmacTripleDes.Stream.RISCV64.keyCall fun _ _ => True := by
  refine RelCT.call (Proof.TripleDes.RISCV64.Key.correct (by lit_decide) (by lit_decide))
    Proof.TripleDes.RISCV64.Key.constantTime [⟨K, KL⟩] [⟨S, 384⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.covers.1, h₁.covers.2, h₂.covers.1, h₂.covers.2⟩
  simp only [Proof.TripleDes.RISCV64.Key.contract, State.withRegions_gpr, State.withRegions_sp,
    State.callEntry_sp, State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs),
    h₁.a0, h₁.a1, h₁.a2, h₂.a0, h₂.a1, h₂.a2, hsp]
  exact ⟨trivial, trivial, trivial, trivial⟩

/-! ## ECB on one block of the state -/

/-- What ECB's call on the block at `S + off` of the state `S` needs. -/
structure EArgs (s : State) (S : Addr) (off : Nat) : Prop where
  a0 : s.gpr .a0 = S
  a1 : s.gpr .a1 = S + BitVec.ofNat 64 off
  a2 : s.gpr .a2 = BitVec.ofInt 64 1
  lo : 384 ≤ off
  hi : off + 8 ≤ 416
  fit : S.toNat + 416 ≤ 2 ^ 64
  al : s.sp.toNat % 16 = 0
  sp : 944 ≤ s.sp.toNat
  stk : (⟨s.sp - 944, 944⟩ : Region).Disjoint ⟨S, 416⟩
  writes : (⟨S, 416⟩ : Region) ∈ s.wr

/-- What ECB's call leaves. -/
structure EPost (s : State) (S : Addr) (off : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  frame : Frame [⟨S + BitVec.ofNat 64 off, 8⟩, ⟨s.sp - 944, 944⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (S + BitVec.ofNat 64 off) 8 =
    Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt s.mem S) (Spec.Aes.bytesAt s.mem (S + BitVec.ofNat 64 off) 8)

theorem EArgs.pre {s : State} {S : Addr} {off : Nat} (h : EArgs s S off) :
    (Proof.TripleDes.RISCV64.Ecb.ecbC .encrypt).pre
      (s.callEntry.withRegions [⟨S, 384⟩] [⟨S + BitVec.ofNat 64 off, 8⟩]) := by
  have hl := h.lo
  have hh := h.hi
  have hf := h.fit
  simp only [Proof.TripleDes.RISCV64.Ecb.ecbC, State.withRegions_gpr, State.withRegions_rd,
    State.withRegions_wr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs),
    h.a0, h.a1, h.a2, show (BitVec.ofInt 64 1).toNat = 1 from rfl, Nat.mul_one]
  refine ⟨trivial, trivial, Offset.base_disjoint _ (by omega) (by omega), ?_, h.al, h.sp,
    h.stk.sub_right (Region.sub_prefix (by decide)), h.stk.sub_right (Offset.sub_base _ (by omega))⟩
  rw [toNat_add_lt S hf (show off < 416 by omega)]; omega

theorem EArgs.covers {s : State} {S : Addr} {off : Nat} (h : EArgs s S off) :
    Covers ([⟨S, 384⟩] ++ [⟨S + BitVec.ofNat 64 off, 8⟩]) (s.rd ++ s.wr) ∧
      Covers [⟨S + BitVec.ofNat 64 off, 8⟩] s.wr := by
  have hh := h.hi
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_append_right _ h.writes, 0, by simp, by show 0 + 384 ≤ 416; decide⟩
    · exact ⟨_, List.mem_append_right _ h.writes, off, rfl, by show off + 8 ≤ 416; omega⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨_, h.writes, off, rfl, by show off + 8 ≤ 416; omega⟩

theorem ecb_call {s : State} {S : Addr} {off : Nat} (h : EArgs s S off) :
    WP isa Impl.CmacTripleDes.Stream.RISCV64.ecbCall s (EPost s S off) := by
  refine WP.callAny (k := Proof.TripleDes.RISCV64.Ecb.ecbC .encrypt) (Proof.TripleDes.RISCV64.Ecb.ecb_ok .encrypt)
    h.pre h.covers.1 h.covers.2 ?_ (by rw [ecb_sdepth]; decide)
  intro s' hrd hwr hsp hf hsaved hpost
  rw [ecb_sdepth] at hf
  refine ⟨hrd, hwr, hsp, hsaved, hf, ?_⟩
  simp only [Proof.TripleDes.RISCV64.Ecb.ecbC, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_mem, State.callEntry_gpr s (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr s (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr s (by decide : Reg.a2 ∉ linkRegs),
    h.a0, h.a1, h.a2, show (BitVec.ofInt 64 1).toNat = 1 from rfl] at hpost
  simp only [Spec.TripleDes.blocksAt, List.range_one, List.map_cons, List.map_nil, Spec.TripleDes.ecb,
    Nat.mul_zero, BitVec.add_zero, List.cons.injEq, and_true] at hpost
  rw [Proof.TripleDes.bytesAt_eq, Proof.TripleDes.bytesAt_eq, hpost]
  rw [Spec.Cmac.tdesWith, ← Proof.TripleDes.bytesAt_eq, Proof.TripleDes.ofFn_bytesAt]

theorem ecb_rel {S : Addr} {off : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → EArgs s₁ S off ∧ EArgs s₂ S off ∧ s₁.sp = s₂.sp) :
    RelCT isa P Impl.CmacTripleDes.Stream.RISCV64.ecbCall fun _ _ => True := by
  refine RelCT.call (Proof.TripleDes.RISCV64.Ecb.ecb_ok .encrypt) Proof.TripleDes.RISCV64.Ecb.encrypt_ct
    [⟨S, 384⟩] [⟨S + BitVec.ofNat 64 off, 8⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.covers.1, h₁.covers.2, h₂.covers.1, h₂.covers.2⟩
  simp only [Proof.TripleDes.RISCV64.Ecb.ecbC, State.withRegions_gpr, State.withRegions_sp,
    State.callEntry_sp, State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs),
    h₁.a0, h₁.a1, h₁.a2, h₂.a0, h₂.a1, h₂.a2, hsp]
  exact ⟨trivial, trivial, trivial, trivial⟩

end VG.Proof.CmacTripleDes.Stream.RISCV64
