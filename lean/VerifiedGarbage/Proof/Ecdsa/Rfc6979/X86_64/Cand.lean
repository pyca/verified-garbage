module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Wide
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Blocks
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy

/-!
# Deterministic ECDSA on x86-64: the candidate

The candidate `T` of RFC 6979's step h.2: the concatenation of successive
`V = HMAC_K(V)`, each appended to the candidate's place `C` in the frame at
the offset `off` (`appendV_ok`: all 64 bytes of `V`'s place, of which the
next `V` overwrites what follows its first `D`), until `off ≥ Q`
(`loopC_ok`): after `i` of them, `C`'s first `i D` bytes are `genT`'s `T` of
`i` `V`s, and the loop stops after RFC 6979's `blocks` (`nb_eq`). The
candidate `k` is `C`'s first `Q` bytes, shifted right by `sh` bits in place
for P-521 (`cand_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

/-- The candidate's offset, in the frame. -/
abbrev offOf {dn : Nat} (L : Lay dn) (m : Mem) : BitVec 64 := m.readW (L.B + BitVec.ofNat 64 152) 64

/-- The number of `V`s in a candidate: RFC 6979's `blocks`. -/
abbrev RfcHash.nb (P : RfcHash) : Nat := Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.H.D

/-- What a candidate changes: `scratch`, the stack below the frame, `K`, `V`
and the offset, and the candidate. -/
abbrev CW {dn : Nat} (L : Lay dn) : List Region :=
  [L.SCR, ⟨L.B, 160⟩, ⟨L.B + BitVec.ofNat 64 384, 136⟩]

/-! ## The number of `V`s -/

/-- After `i` `V`s fewer than `Q` bytes, and after `i + 1` at least: `i + 1`
is RFC 6979's `blocks`, as `qlen` is within `Q`'s last byte. -/
theorem nb_eq {i : Nat} (h₁ : i * P.H.D < P.Q) (h₂ : P.Q ≤ (i + 1) * P.H.D) : P.nb = i + 1 := by
  have hl := P.R.nBits_len
  have hD : 0 < P.H.D := by nums
  have hQ : P.Q = P.R.E.C.len := rfl
  have e₁ : (i + 1) * P.H.D = i * P.H.D + P.H.D := Nat.succ_mul _ _
  rw [RfcHash.nb, Spec.Ecdsa.Rfc6979.blocks]
  refine Nat.div_eq_of_lt_le ?_ ?_
  · rw [show (i + 1) * (8 * P.H.D) = 8 * (i * P.H.D) + 8 * P.H.D by
      rw [Nat.mul_comm 8, ← Nat.mul_assoc, e₁, Nat.add_mul, Nat.mul_comm (i * P.H.D), Nat.mul_comm P.H.D]]
    omega
  · rw [show (i + 1 + 1) * (8 * P.H.D) = 8 * (i * P.H.D) + 8 * P.H.D + 8 * P.H.D by
      rw [Nat.succ_mul, Nat.mul_comm 8, ← Nat.mul_assoc, e₁, Nat.add_mul, Nat.mul_comm (i * P.H.D), Nat.mul_comm P.H.D]]
    omega

/-- A candidate's `V`s make at least `Q` bytes. -/
theorem nb_len : P.Q ≤ P.nb * P.H.D ∧ 1 ≤ P.nb := by
  have hl := P.R.nBits_len
  have hD : 0 < P.H.D := by nums
  have hQ : P.Q = P.R.E.C.len := rfl
  have hQ8 : 8 ≤ P.Q := by nums
  rw [RfcHash.nb, Spec.Ecdsa.Rfc6979.blocks]
  generalize hN : Spec.Ecdsa.nBits P.R.E.C = N at hl ⊢
  have h := Nat.lt_mul_div_succ (N + 8 * P.H.D - 1) (show 0 < 8 * P.H.D by omega)
  generalize (N + 8 * P.H.D - 1) / (8 * P.H.D) = b at h ⊢
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at h
  rw [Nat.mul_comm b]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [Nat.mul_zero] at h; omega
  · omega

/-! ## `T`, one `V` at a time -/

theorem genT_succ (H : Spec.Hmac.HashFunction) (K : List Byte) : ∀ (i : Nat) (V : List Byte),
    Spec.Ecdsa.Rfc6979.genT H K (i + 1) V =
      ((Spec.Ecdsa.Rfc6979.genT H K i V).1 ++ Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K i V).2,
        Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K i V).2)
  | 0, _ => by simp [Spec.Ecdsa.Rfc6979.genT]
  | i + 1, V => by
    rw [show Spec.Ecdsa.Rfc6979.genT H K (i + 1 + 1) V = (Spec.Hmac.hmac H K V ++
        (Spec.Ecdsa.Rfc6979.genT H K (i + 1) (Spec.Hmac.hmac H K V)).1,
        (Spec.Ecdsa.Rfc6979.genT H K (i + 1) (Spec.Hmac.hmac H K V)).2) from rfl,
      show Spec.Ecdsa.Rfc6979.genT H K (i + 1) V = (Spec.Hmac.hmac H K V ++
        (Spec.Ecdsa.Rfc6979.genT H K i (Spec.Hmac.hmac H K V)).1,
        (Spec.Ecdsa.Rfc6979.genT H K i (Spec.Hmac.hmac H K V)).2) from rfl,
      genT_succ H K i (Spec.Hmac.hmac H K V)]
    simp

theorem genT_length (K V : List Byte) : ∀ i,
    (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K i V).1.length = i * P.H.D
  | 0 => by simp [Spec.Ecdsa.Rfc6979.genT]
  | i + 1 => by
    rw [genT_succ, List.length_append, genT_length K V i, Nat.succ_mul]
    exact congrArg _ (mac_length P _ _)

/-! ## Appending one `V` -/

/-- The offset 0. -/
theorem offInit_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.offInit) t fun t' => Ctx L g m₀ t' ∧ Frame [⟨L.B + BitVec.ofNat 64 152, 8⟩] t.mem t'.mem ∧
      offOf L t'.mem = 0 := by
  have w := hc.inFrW (d := 152) (n := 8) (by omega) (by have := L.he; omega)
  refine Ctx.of_keep hL hc ?_ (by decide) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)
  apply WP.of_runBlock
  simp only [Cfg.offInit, fOff, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32,
    State.setReg32, State.store64, ea_stk, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_false, ite_true, RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.mem_setReg,
    RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, hc.rsp, Offset.add_add, Nat.reduceAdd, w,
    Option.some.injEq, exists_eq_left', xor_self_zx]
  exact ⟨by triv, by triv, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _),
    Mem.readW_writeW_self64 _ _ _⟩

/-- `V`'s 64 bytes to the candidate at the offset `off`, through `rdx`
holding `rsp + off`. -/
theorem copyC_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {off : Nat} (ho : off ≤ 72)
    (hdx : u.gpr .rdx = L.B + BitVec.ofNat 64 (24 + off)) :
    WP isa (.block (Cfg.copyN 8 .rsp fV .rdx fC)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .rax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.B + BitVec.ofNat 64 (384 + off), 64⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (384 + off)) 64 =
        Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 88) 64 := by
  have he := L.he
  have e : ∀ x, L.B + BitVec.ofNat 64 (24 + off) + BitVec.ofNat 64 x = L.B + BitVec.ofNat 64 (24 + off + x) :=
    fun x => Offset.add_add _ _ _
  have hsep : Region.Disjoint ⟨L.B + BitVec.ofNat 64 24 + BitVec.ofNat 64 64, 8 * 8⟩
      ⟨L.B + BitVec.ofNat 64 (24 + off) + BitVec.ofNat 64 360, 8 * 8⟩ := by
    rw [fr_add, e]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
  have hr : ∀ j < 8, InRegions (u.rd ++ u.wr) (L.B + BitVec.ofNat 64 24 + BitVec.ofNat 64 (64 + 8 * j)) 8 :=
    fun j hj => by rw [fr_add]; exact hc.inFr (by omega) (by omega)
  have hw : ∀ j < 8, InRegions u.wr (L.B + BitVec.ofNat 64 (24 + off) + BitVec.ofNat 64 (360 + 8 * j)) 8 :=
    fun j hj => by rw [e]; exact hc.inFrW (by omega) (by omega)
  refine WP.mono_syms (copyN_ok (src := .rsp) (dst := .rdx) (S := L.B + BitVec.ofNat 64 24)
      (D := L.B + BitVec.ofNat 64 (24 + off)) (so := 64) (d := 360) (K := 8) (by decide) (by decide) hsep
      (by omega) 8 (Nat.le_refl _) u hc.rsp hdx hr hw)
    fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy => ?_
  rw [e, show 24 + off + 360 = 384 + off by omega] at hf hb
  rw [fr_add] at hb
  exact ⟨hc.keep hL hrd hwr (hg _ (by decide)) (fun r hr _ => hg r (ne_cs hr (by decide))) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega) (by omega)) hsy,
    hg, hf, hb⟩

theorem sx32' {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := sx32 h

/-- The offset `D` more, and the carry flag set iff it is below `Q`. -/
theorem offStep_ok (hL : L.Ok) (hq : HashLay P L) {u : State} (hc : Ctx L g m₀ u) {off : Nat} (ho : off ≤ 72)
    (hoff : offOf L u.mem = BitVec.ofNat 64 off) :
    WP isa (.block [.mov .rcx (.mem (stk fOff)), .alu .add .rcx (.mem (stk fHL)), .store (stk fOff) .rcx,
      .alu .cmp .rcx (.imm (BitVec.ofNat 32 P.Q))]) u fun u' => Ctx L g m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 152, 8⟩] u.mem u'.mem ∧ offOf L u'.mem = BitVec.ofNat 64 (off + P.H.D) ∧
      u'.cf = some (decide (off + P.H.D < P.Q)) := by
  rw [show ([.mov .rcx (.mem (stk fOff)), .alu .add .rcx (.mem (stk fHL)), .store (stk fOff) .rcx,
      .alu .cmp .rcx (.imm (BitVec.ofNat 32 P.Q))] : List Instr) = [.mov .rcx (.mem (stk fOff))] ++
      [.alu .add .rcx (.mem (stk fHL))] ++ [.store (stk fOff) .rcx, .alu .cmp .rcx (.imm (BitVec.ofNat 32 P.Q))]
      from rfl, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ld_ok hL hc (d := .rcx) (by decide) (o := fOff) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (addHL_ok hL hq h₁.ctx (d := .rcx) (by decide)) fun u₂ h₂ => ?_
  have hoff' : u.mem.readW (L.B + BitVec.ofNat 64 (24 + fOff)) 64 = BitVec.ofNat 64 off := hoff
  have hcx : u₂.gpr .rcx = BitVec.ofNat 64 (off + P.H.D) := by
    rw [h₂.val, h₁.val, hoff', BitVec.ofNat_add_ofNat]
  have hc₂ := h₂.ctx
  have w := hc₂.inFrW (d := 152) (n := 8) (by omega) (by have := L.he; omega)
  have hQ : P.Q < 2 ^ 31 := by nums
  refine WP.mono (Ctx.of_keep (Q := fun u' => offOf L u'.mem = BitVec.ofNat 64 (off + P.H.D) ∧
      u'.cf = some (decide (off + P.H.D < P.Q))) (ws := [⟨L.B + BitVec.ofNat 64 152, 8⟩]) hL hc₂ ?_ (by rfl)
      (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)))
    fun u' ⟨hc', hf, ho', hcf⟩ => ⟨hc', by rw [← h₁.mem, ← h₂.mem]; exact hf, ho', hcf⟩
  apply WP.of_runBlock
  simp only [fOff, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.store64, ea_stk,
    hc₂.rsp, Offset.add_add, Nat.reduceAdd, w, ite_true, hcx, sx32' hQ, Option.bind_some, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, RegUpd.cf_arithFlags, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _),
    Mem.readW_writeW_self64 _ _ _, ?_⟩
  have h₁ : (BitVec.ofNat 64 (off + P.H.D)).toNat = off + P.H.D := by rw [BitVec.toNat_ofNat]; nums
  have h₂ : (BitVec.ofNat 64 P.Q).toNat = P.Q := by rw [BitVec.toNat_ofNat]; nums
  rw [h₁, h₂]

/-- `V` appended to the candidate at the offset `off`, and the offset `D` more,
the carry flag set iff it is below `Q`. -/
theorem appendV_ok (hL : L.Ok) (hq : HashLay P L) {u : State} (hc : Ctx L g m₀ u) {off : Nat} (ho : off ≤ 72)
    (hoff : offOf L u.mem = BitVec.ofNat 64 off) (hdx : u.gpr .rdx = BitVec.ofNat 64 off) :
    WP isa (.block (cfgOf P).appendV) u fun u' => Ctx L g m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 (384 + off), 64⟩, ⟨L.B + BitVec.ofNat 64 152, 8⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (384 + off)) 64 =
        Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 88) 64 ∧
      offOf L u'.mem = BitVec.ofNat 64 (off + P.H.D) ∧ u'.cf = some (decide (off + P.H.D < P.Q)) := by
  rw [Cfg.appendV, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (addReg_ok hL hc (d := .rdx) (by decide) .rsp) fun u₁ h₁ => ?_
  have hdx₁ : u₁.gpr .rdx = L.B + BitVec.ofNat 64 (24 + off) := by
    rw [h₁.val, hdx, hc.rsp, BitVec.add_comm, Offset.add_add]
  refine WP.mono (copyC_ok hL h₁.ctx ho hdx₁) fun u₂ ⟨hc₂, _, hf₂, hb₂⟩ => ?_
  have hoff₂ : offOf L u₂.mem = BitVec.ofNat 64 off := by
    rw [← hoff, ← h₁.mem]
    exact hf₂.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)
  refine WP.mono (offStep_ok hL hq hc₂ ho hoff₂) fun u₃ ⟨hc₃, hf₃, ho₃, hcf₃⟩ => ⟨hc₃, ?_, ?_, ho₃, hcf₃⟩
  · rw [← h₁.mem]
    exact (hf₂.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩).trans (hf₃.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
  · rw [bytesAt_frame hf₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), hb₂, h₁.mem]

/-! ## The loop -/

/-- After `i` `V`s from `K` and `V`: `K`, the last `V`, the candidate's first
`i D` bytes and the offset, with memory changed only where a candidate
changes it since `t₀`. -/
structure CInv (P : RfcHash) {dn : Nat} (L : Lay dn) (t₀ : State) (K V : List Byte) (i : Nat) (t : State) : Prop where
  frame : Frame (CW L) t₀.mem t.mem
  k : kOf P L t.mem = K
  v : vOf P L t.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K i V).2
  c : Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 384) (i * P.H.D) = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K i V).1
  off : offOf L t.mem = BitVec.ofNat 64 (i * P.H.D)

theorem kvw_cw : ∀ r ∈ KVW L, ∃ r' ∈ CW L, Region.Sub r r' := fun r hr => by
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, by simp, sub_refl _⟩
  · exact ⟨⟨L.B, 160⟩, by simp, Region.sub_prefix (by omega)⟩

/-- One `V` more. -/
theorem candStep_ok (hL : L.Ok) (hq : HashLay P L) {t₀ t : State} (hc : Ctx L g m₀ t) {K V : List Byte} {i : Nat}
    (hi : CInv P L t₀ K V i t) (hlt : i * P.H.D < P.Q) :
    WP isa (cfgOf P).candStep t fun t' => Ctx L g m₀ t' ∧ CInv P L t₀ K V (i + 1) t' ∧
      t'.cf = some (decide ((i + 1) * P.H.D < P.Q)) := by
  have hQ : P.Q ≤ 66 := by nums
  have hD : P.H.D ≤ 64 := by nums
  have e₁ : (i + 1) * P.H.D = i * P.H.D + P.H.D := Nat.succ_mul _ _
  refine WP.seq (WP.mono (hmacV_ok hL hq hc) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁⟩ => ?_)
  have hoff₁ : offOf L u₁.mem = BitVec.ofNat 64 (i * P.H.D) := by
    rw [← hi.off]
    exact hf₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by have := L.he; omega)
      · exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)
  refine WP.seq (WP.mono (ld_ok hL hc₁ (d := .rdx) (by decide) (o := fOff) (by decide)) fun u₂ h₂ => ?_)
  have hdx₂ : u₂.gpr .rdx = BitVec.ofNat 64 (i * P.H.D) := h₂.val.trans hoff₁
  rw [← h₂.mem] at hoff₁
  refine WP.mono (appendV_ok hL hq h₂.ctx (by omega) hoff₁ hdx₂) fun u₃ ⟨hc₃, hf₃, hb₃, ho₃, hcf₃⟩ =>
    ⟨hc₃, ⟨?_, ?_, ?_, ?_, by rw [ho₃, e₁]⟩, by rw [hcf₃, e₁]⟩
  · refine (hi.frame.trans (hf₁.sub kvw_cw)).trans (h₂.mem ▸ hf₃.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp, Offset.sub (e := 384) (k := 136) _ (by omega) (by omega)⟩
    · exact ⟨⟨L.B, 160⟩, by simp, Offset.sub_base _ (by omega)⟩
  · rw [show kOf P L u₃.mem = kOf P L u₁.mem by
      rw [← h₂.mem]; exact bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint _ (by omega) (by nums) (by omega)
        · exact Offset.disjoint _ (by omega) (by nums) (by omega)) (by nums), hk₁, hi.k]
  · have hv₃ : vOf P L u₃.mem = vOf P L u₁.mem := by
      rw [← h₂.mem]
      exact bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint _ (by omega) (by nums) (by omega)
        · exact Offset.disjoint _ (by omega) (by nums) (by omega)) (by nums)
    rw [genT_succ]
    dsimp only
    rw [hv₃, hv₁, hi.k, hi.v]
  · rw [e₁, Proof.Hmac.Common.bytesAt_add, Offset.add_add, genT_succ]
    have hT : Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 384) (i * P.H.D) =
        (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K i V).1 := by
      rw [← hi.c, bytesAt_frame hf₃ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint _ (by omega) (by omega) (by omega)
          · exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega), h₂.mem]
      exact bytesAt_frame hf₁ (fun r hr => by
        simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_SCR (by have := L.he; omega)
        · exact Offset.disjoint_base _ (by omega) (by omega)) (by omega)
    rw [hT]
    refine congrArg (_ ++ ·) ?_
    rw [bytesAt_take _ _ (k := 64) hD, hb₃, ← bytesAt_take _ _ hD, h₂.mem]
    show vOf P L u₁.mem = _
    rw [hv₁, hi.k, hi.v]

/-- One `V` more, as far as the offset and the flag go. -/
theorem candStepOff_ok (hL : L.Ok) (hq : HashLay P L) {t : State} (hc : Ctx L g m₀ t) {off : Nat} (ho : off ≤ 72)
    (hoff : offOf L t.mem = BitVec.ofNat 64 off) :
    WP isa (cfgOf P).candStep t fun t' => Ctx L g m₀ t' ∧ offOf L t'.mem = BitVec.ofNat 64 (off + P.H.D) ∧
      t'.cf = some (decide (off + P.H.D < P.Q)) := by
  refine WP.seq (WP.mono (hmacV_ok hL hq hc) fun u₁ ⟨hc₁, hf₁, _, _⟩ => ?_)
  have hoff₁ : offOf L u₁.mem = BitVec.ofNat 64 off := by
    rw [← hoff]
    exact hf₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by have := L.he; omega)
      · exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)
  refine WP.seq (WP.mono (ld_ok hL hc₁ (d := .rdx) (by decide) (o := fOff) (by decide)) fun u₂ h₂ => ?_)
  have hdx₂ : u₂.gpr .rdx = BitVec.ofNat 64 off := h₂.val.trans hoff₁
  rw [← h₂.mem] at hoff₁
  exact WP.mono (appendV_ok hL hq h₂.ctx ho hoff₁ hdx₂) fun u₃ ⟨hc₃, _, _, ho₃, hcf₃⟩ => ⟨hc₃, ho₃, hcf₃⟩

/-- The loop: `V`s appended until there are `Q` bytes, RFC 6979's `blocks`. -/
theorem loopC_ok (hL : L.Ok) (hq : HashLay P L) {t : State} (hc : Ctx L g m₀ t) (hoff : offOf L t.mem = 0) :
    WP isa (.loop (cfgOf P).candStep .b) t fun t' => Ctx L g m₀ t' ∧
      CInv P L t (kOf P L t.mem) (vOf P L t.mem) P.nb t' := by
  have hQ8 : 8 ≤ P.Q := by nums
  refine WP.loop (M := isa) (fun n (s : State) => Ctx L g m₀ s ∧ n ≤ P.nb ∧
      CInv P L t (kOf P L t.mem) (vOf P L t.mem) (P.nb - n) s ∧ (P.nb - n) * P.H.D < P.Q) ?_ P.nb t
    ⟨hc, Nat.le_refl _, ⟨Frame.refl _ _, rfl, by rw [Nat.sub_self]; rfl, by rw [Nat.sub_self, Nat.zero_mul]; rfl,
      by rw [Nat.sub_self, Nat.zero_mul, hoff]; rfl⟩, by rw [Nat.sub_self, Nat.zero_mul]; omega⟩
  rintro n s ⟨hcs, hn, hi, hlt⟩
  refine WP.mono (candStep_ok hL hq hcs hi hlt) fun s' ⟨hc', hi', hcf⟩ => ?_
  by_cases hgo : (P.nb - n + 1) * P.H.D < P.Q
  · refine .inr ⟨by show s'.cf = _; rw [hcf, decide_eq_true hgo], n - 1, ?_, hc', by omega, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos n with rfl | h
      · exact absurd (Nat.lt_of_lt_of_le hlt (by rw [Nat.sub_zero]; exact nb_len.1)) (Nat.lt_irrefl _)
      · omega
    · have : P.nb - (n - 1) = P.nb - n + 1 := by
        rcases Nat.eq_zero_or_pos n with rfl | h
        · exact absurd (Nat.lt_of_lt_of_le hlt (by rw [Nat.sub_zero]; exact nb_len.1)) (Nat.lt_irrefl _)
        · omega
      rw [this]; exact hi'
    · have : P.nb - (n - 1) = P.nb - n + 1 := by
        rcases Nat.eq_zero_or_pos n with rfl | h
        · exact absurd (Nat.lt_of_lt_of_le hlt (by rw [Nat.sub_zero]; exact nb_len.1)) (Nat.lt_irrefl _)
        · omega
      rw [this]; exact hgo
  · refine .inl ⟨by show s'.cf = _; rw [hcf, decide_eq_false hgo], hc', ?_⟩
    rw [nb_eq hlt (by omega)]
    exact hi'

/-- `scratch` in `rdi`. -/
theorem scrPtr_ok' (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.scrPtr) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .rdi = L.scr := scrPtr_ok hL hc

/-- The candidate: `V = HMAC_K(V)`, RFC 6979's `blocks` times, and `k`, whose
number is `bits2int` of the candidate, at `kArg`. -/
theorem cand_ok (hL : L.Ok) (hq : HashLay P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ Frame (CW L) t.mem u.mem ∧ kOf P L u.mem = kOf P L t.mem ∧
      vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) P.nb (vOf P L t.mem)).2 ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kArg P L) P.Q) =
        Spec.Ecdsa.Rfc6979.bits2int P.R.E.C
          (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) P.nb (vOf P L t.mem)).1 := by
  have hl := P.R.nBits_len
  have hsh := P.R.sh_wide
  have hlen := genT_length (P := P) (kOf P L t.mem) (vOf P L t.mem) P.nb
  have hnb := (nb_len (P := P)).1
  refine WP.seq (WP.mono (offInit_ok hL hc) fun u₁ ⟨hc₁, hf₁, ho₁⟩ => ?_)
  have hk₁ : kOf P L u₁.mem = kOf P L t.mem := bytesAt_frame hf₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums)) (by nums)
  have hv₁ : vOf P L u₁.mem = vOf P L t.mem := bytesAt_frame hf₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by nums)) (by nums)
  have hf₁' : Frame (CW L) t.mem u₁.mem := hf₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨L.B, 160⟩, by simp, Offset.sub_base _ (by omega)⟩
  rw [← hk₁, ← hv₁] at hlen ⊢
  cases hw : P.R.wide
  · have hsh0 : P.R.sh = 0 := by rw [hsh, hw]; rfl
    have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by
      have := (P.R.sizesA hw).2.2.1; show _ = 8 * P.R.E.C.len; omega
    have e : (cfgOf P).sh = 0 := hsh0
    simp only [e, ite_true]
    refine WP.mono (loopC_ok hL hq hc₁ ho₁) fun u ⟨hcu, hi⟩ => ⟨hcu, hf₁'.trans hi.frame, hi.k, hi.v, ?_⟩
    rw [Spec.Ecdsa.Rfc6979.bits2int, hashToInt_takeQ hB (by rw [hlen]; exact hnb), ← hi.c,
      ← bytesAt_take _ _ hnb]
  · have hsh7 : P.R.sh = 7 := by rw [hsh, hw]; rfl
    obtain ⟨hw9, hQ66⟩ := P.sizesW hw
    have e : (cfgOf P).sh = 7 := hsh7
    simp only [e, Nat.reduceEqDiff, ite_false]
    refine WP.seq (WP.mono (loopC_ok hL hq hc₁ ho₁) fun u₂ ⟨hc₂, hi⟩ => ?_)
    refine WP.seq (WP.mono (scrPtr_ok' hL hc₂) fun u₃ ⟨hc₃, hm₃, hdi₃⟩ => ?_)
    refine WP.mono (conv_ok hL hw hc₃ hdi₃ (o := fC) (s := 7) (by decide) (by decide) (by decide) (by decide))
      fun u ⟨hcu, _, hf, hb⟩ => ⟨hcu, ?_, ?_, ?_, ?_⟩
    · refine (hf₁'.trans hi.frame).trans (hm₃ ▸ hf.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨L.SCR, by simp, Offset.sub_base (k := 8192) _ (by omega)⟩
      · exact ⟨⟨L.B + BitVec.ofNat 64 384, 136⟩, by simp, Region.sub_prefix (by rw [hQ66]; decide)⟩
    · rw [← hi.k, ← hm₃]
      exact bytesAt_frame hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr (by have := L.he; nums) (by omega)
        · exact Offset.disjoint _ (by have : fC = 360 := rfl; nums) (by nums) (by have : fC = 360 := rfl; nums)) (by nums)
    · rw [← hi.v, ← hm₃]
      exact bytesAt_frame hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr (by have := L.he; nums) (by omega)
        · exact Offset.disjoint _ (by have : fC = 360 := rfl; nums) (by nums) (by have : fC = 360 := rfl; nums)) (by nums)
    · show Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + fC)) P.Q) = _
      rw [hb, hm₃, Spec.Ecdsa.Rfc6979.bits2int,
        hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega) (by rw [hlen]; exact hnb),
        show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = 7 by show 8 * P.R.E.C.len - _ = 7; omega,
        ← hi.c, ← bytesAt_take _ _ hnb]
      refine ofBytes_toBytes _ _ (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) ?_)
      have := ofBytes_lt (Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (24 + fC)) P.Q)
      rwa [show (Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (24 + fC)) P.Q).length = P.Q by
        simp [Spec.Sha256.bytesAt]] at this

end VG.Proof.Ecdsa.Rfc6979.X86_64
