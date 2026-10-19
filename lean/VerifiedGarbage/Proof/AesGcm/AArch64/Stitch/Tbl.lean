module

public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ops
public import VerifiedGarbage.Impl.AesGcm.AArch64.Stitch
public import VerifiedGarbage.Spec.Gcm.Powers8
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block

/-!
# AES-GCM on AArch64, interleaved: the table of keys

Untrusted: everything here is checked by Lean. The powers `H'ᵏ = pp H k`
in `tReg k`, with their halves swapped in `sReg k` (`PInv`): computed from
`H'` by `vg_ghash_aes`'s `powers` (`powers_ok`, from `PrepPow`, the
algebra's one fact, a hypothesis here), or loaded from a buffer of
`Spec.Gcm.Powers8Repr` (`loadPws_ok`); and stored as the table of keys
(`tbl_ok`: `Stitch.TblOk`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Stitch

open VG VG.AArch64
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV sp_setV)
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly pp PrepPow mulV mulV_ok swap_ok tReg_free sReg_free
  tReg_inj sReg_inj tReg_ne_sReg ext8_ext8 ext8_eq vdword_ext8_0 vdword_ext8_1 vdwords vdword_xor
  exec_eor exec_ext8)
open VG.Proof.Gcm.AArch64.Stitch (TblOk kpack kkey)
open VG.Impl.Gcm.AArch64.Pmull (LO MID HI T C tReg sReg poly)
open VG.Impl.Gcm.AArch64.Stitch (sOff kOff pk pl)
open VG.Spec.Gcm (Block)

/-- The powers `H'` to `H'ᴷ` in `tReg`, with their halves swapped in
`sReg`, and the reduction constant. -/
structure PInv (H : Block) (K : Nat) (s : State) : Prop where
  c : s.v C = ofVDwords poly poly
  t : ∀ k, 1 ≤ k → k ≤ K → s.v (tReg k) = pp H k
  sw : ∀ k, 1 ≤ k → k ≤ K → s.v (sReg k) = ext8 (pp H k) (pp H k)

/-- The powers `H'` to `H'ᴷ` in `tReg`, with their halves swapped in
`sReg` (`PInv` without the reduction constant). -/
structure PT (H : Block) (K : Nat) (s : State) : Prop where
  t : ∀ k, 1 ≤ k → k ≤ K → s.v (tReg k) = pp H k
  sw : ∀ k, 1 ≤ k → k ≤ K → s.v (sReg k) = ext8 (pp H k) (pp H k)

theorem PInv.pt {H : Block} {K : Nat} {s : State} (h : PInv H K s) : PT H K s := ⟨h.t, h.sw⟩

/-- The registers `powers` writes. -/
abbrev powV : List VReg :=
  [LO, MID, HI, T, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v25, .v26, .v27, .v28, .v29, .v30, .v31]

theorem tReg_mem (k : Nat) (h2 : 2 ≤ k) (h8 : k ≤ 8) : tReg k ∈ powV := by
  rcases (by omega : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem sReg_mem (k : Nat) (h2 : 2 ≤ k) (h8 : k ≤ 8) : sReg k ∈ powV := by
  rcases (by omega : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem tReg_ne_C (k : Nat) : tReg k ≠ C := by unfold tReg; split <;> decide
theorem sReg_ne_C (k : Nat) : sReg k ≠ C := by unfold sReg; split <;> decide

theorem tReg_nmem (k : Nat) : tReg k ∉ [LO, MID, HI, T] := by unfold tReg; split <;> decide
theorem sReg_nmem (k : Nat) : sReg k ∉ [LO, MID, HI, T] := by unfold sReg; split <;> decide

/-- `H'ᴷ⁺¹ = mul(H'ⁱ, H'ʲ)`, as a prepared power. -/
theorem pow_ok (hP : PrepPow) {H : Block} {K i j : Nat} (hi : 1 ≤ i) (hiK : i ≤ K) (hj : 1 ≤ j) (hjK : j ≤ K)
    (hij : i + j = K + 1) (hK : K + 1 ≤ 8) {s : State} (hI : PInv H K s) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.pow (K + 1) i j)) s fun s' =>
      PInv H (K + 1) s' ∧ VOnly [LO, MID, HI, T, sReg (K + 1), tReg (K + 1)] s s' := by
  rw [Impl.Gcm.AArch64.Pmull.pow, WP.block_append_iff]
  refine WP.mono (mulV_ok (sReg (K + 1)) (sReg i) (sReg j) (tReg j) s (sReg_free _) (sReg_free _)
    (tReg_free _) (by rw [hI.sw j hj hjK, hI.t j hj hjK]) hI.c) fun s₁ ⟨m₁, o₁⟩ => ?_
  refine WP.mono (swap_ok (tReg (K + 1)) (sReg (K + 1)) s₁) fun s' ⟨w, o₂⟩ => ?_
  have O : VOnly [LO, MID, HI, T, sReg (K + 1), tReg (K + 1)] s s' := (o₁.trans o₂).weaken fun r hr => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with (h | h | h | h | h) | h <;> simp [h]
  have hs₁ : s₁.v (sReg (K + 1)) = ext8 (pp H (K + 1)) (pp H (K + 1)) := by
    rw [m₁, hI.sw i hi hiK, hI.t j hj hjK, hP.mul, hij]
  have ks : s'.v (sReg (K + 1)) = s₁.v (sReg (K + 1)) := o₂.v _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; exact fun e => tReg_ne_sReg _ _ e.symm)
  have kv : ∀ k, 1 ≤ k → k ≤ K → s'.v (tReg k) = s.v (tReg k) ∧ s'.v (sReg k) = s.v (sReg k) := by
    intro k hk hkK
    have ht : tReg k ≠ tReg (K + 1) := fun e => by have := tReg_inj k (by omega) (K + 1) (by omega) hk (by omega) e; omega
    have hs : sReg k ≠ sReg (K + 1) := fun e => by have := sReg_inj k (by omega) (K + 1) (by omega) hk (by omega) e; omega
    refine ⟨O.v _ ?_, O.v _ ?_⟩
    · have := tReg_nmem k
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2, tReg_ne_sReg _ _, ht⟩
    · have := sReg_nmem k
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at this ⊢
      exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2, hs, fun e => tReg_ne_sReg _ _ e.symm⟩
  have hC : C ∉ [LO, MID, HI, T, sReg (K + 1), tReg (K + 1)] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨by decide, by decide, by decide, by decide, (sReg_ne_C _).symm, (tReg_ne_C _).symm⟩
  refine ⟨⟨by rw [O.v C hC, hI.c], fun k hk hkK => ?_, fun k hk hkK => ?_⟩, O⟩
  · rcases (by omega : k = K + 1 ∨ k ≤ K) with rfl | hkK'
    · rw [w, hs₁, ext8_ext8]
    · rw [(kv k hk hkK').1, hI.t k hk hkK']
  · rcases (by omega : k = K + 1 ∨ k ≤ K) with rfl | hkK'
    · rw [ks, hs₁]
    · rw [(kv k hk hkK').2, hI.sw k hk hkK']

/-- `powers`: `H'` to `H'⁸` from `H'`. -/
theorem powers_ok (hP : PrepPow) {H : Block} {s : State} (hI : PInv H 1 s) :
    WP isa (.block Impl.Gcm.AArch64.Pmull.powers) s fun s' => PInv H 8 s' ∧ VOnly powV s s' := by
  have step : ∀ {K i j : Nat} {u : State} {rest : List Instr} {Q : State → Prop}, 1 ≤ i → i ≤ K → 1 ≤ j →
      j ≤ K → i + j = K + 1 → K + 1 ≤ 8 → PInv H K u → VOnly powV s u →
      (∀ u', PInv H (K + 1) u' → VOnly powV s u' → WP isa (.block rest) u' Q) →
      WP isa (.block (Impl.Gcm.AArch64.Pmull.pow (K + 1) i j ++ rest)) u Q := by
    intro K i j u rest Q hi hiK hj hjK hij hK hu ou hQ
    rw [WP.block_append_iff]
    refine WP.mono (pow_ok hP hi hiK hj hjK hij hK hu) fun u' ⟨h', o'⟩ => hQ u' h' ((ou.trans o').weaken ?_)
    intro r hr
    rcases List.mem_append.mp hr with h | h
    · exact h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      any_goals decide
      · exact sReg_mem _ (by omega) hK
      · exact tReg_mem _ (by omega) hK
  have o₀ : VOnly powV s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [← List.append_nil Impl.Gcm.AArch64.Pmull.powers]
  simp only [Impl.Gcm.AArch64.Pmull.powers, List.append_assoc]
  exact step (K := 1) (i := 1) (j := 1) (by decide) (by decide) (by decide) (by decide) rfl (by decide) hI o₀
    fun _ h o => step (K := 2) (i := 2) (j := 1) (by decide) (by decide) (by decide) (by decide) rfl (by decide) h o
    fun _ h o => step (K := 3) (i := 2) (j := 2) (by decide) (by decide) (by decide) (by decide) rfl (by decide) h o
    fun _ h o => step (K := 4) (i := 4) (j := 1) (by decide) (by decide) (by decide) (by decide) rfl (by decide) h o
    fun _ h o => step (K := 5) (i := 4) (j := 2) (by decide) (by decide) (by decide) (by decide) rfl (by decide) h o
    fun _ h o => step (K := 6) (i := 4) (j := 3) (by decide) (by decide) (by decide) (by decide) rfl (by decide) h o
    fun _ h o => step (K := 7) (i := 4) (j := 4) (by decide) (by decide) (by decide) (by decide) rfl (by decide) h o
    fun _ h o => WP.block_nil ⟨h, o⟩

/-! ## The table -/

/-- Where the table is. -/
abbrev tblR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 512, 192⟩

theorem readW_write_self (m : Mem) (a : Addr) (v : BitVec 128) : (m.write a 16 v).readW a 128 = v := by
  show BitVec.setWidth 128 ((m.write a 16 v).read a 16) = v
  rw [BitVec.setWidth_eq]
  exact Mem.read_eq_of_bytes fun i hi => by
    simp only [Mem.write, Mem.sub_ofNat_toNat a (show i < 2 ^ 64 by omega), hi, ite_true]

theorem readW_write_sep {m : Mem} {W : Addr} {d e : Nat} {v : BitVec 128} (h : d + 16 ≤ e ∨ e + 16 ≤ d)
    (hd : d + 16 ≤ 2 ^ 64) (he : e + 16 ≤ 2 ^ 64) :
    (m.write (W + BitVec.ofNat 64 e) 16 v).readW (W + BitVec.ofNat 64 d) 128 =
      m.readW (W + BitVec.ofNat 64 d) 128 := by
  show BitVec.setWidth 128 ((m.write _ 16 v).read _ 16) = BitVec.setWidth 128 (m.read _ 16)
  rw [Mem.read_write_sep (Offset.sep W h hd he) (by decide)]

/-- A store into the table. -/
theorem st_ok (t : VReg) {d : Nat} (hd : 512 ≤ d) (hd' : d + 16 ≤ 704) (h16 : d % 16 = 0) {s : State}
    (hw : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 512) 192) :
    WP isa (.block [.strq t .x19 d]) s fun s' =>
      s' = { s with mem := s.mem.write (s.gpr .x19 + BitVec.ofNat 64 d) 16 (s.v t) } ∧
      Frame [tblR (s.gpr .x19)] s.mem s'.mem := by
  have hin : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 16 := by
    have := CallLay.inRegions_sub (off := d - 512) (l := 16) hw (by omega) (by decide)
    rwa [Offset.add_add, show 512 + (d - 512) = d by omega] at this
  refine WP.block_cons_iff.mpr ⟨_, Proof.Gcm.AArch64.Pmull.exec_strq h16 (by omega) hin, WP.block_nil ⟨rfl, ?_⟩⟩
  exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Offset.contains _ hd (by omega) (by decide))

/-- The table's first `n` powers and `q` pairs of keys stored. -/
structure TS (s₀ : State) (H : Block) (n q : Nat) (s : State) : Prop where
  v : ∀ r, r ∉ [VReg.v2, .v3, .v4] → s.v r = s₀.v r
  gpr : s.gpr = s₀.gpr
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [tblR (s₀.gpr .x19)] s₀.mem s.mem
  sw : ∀ k < n, s.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (sOff (k + 1))) 128 = ext8 (pp H (k + 1)) (pp H (k + 1))
  key : ∀ p < q, s.mem.readW (s₀.gpr .x19 + BitVec.ofNat 64 (kOff p)) 128 = kpack H (pk p) (pl p)

theorem sOff_eq (k : Nat) : sOff (k + 1) = 512 + 16 * k := by
  unfold sOff Impl.Gcm.AArch64.Stitch.tbl; omega

theorem kOff_eq (p : Nat) : kOff p = 640 + 16 * p := by
  unfold kOff Impl.Gcm.AArch64.Stitch.tbl; omega

theorem pkl_range : ∀ p < 4, 1 ≤ pk p ∧ pk p ≤ 8 ∧ 1 ≤ pl p ∧ pl p ≤ 8 := by decide

theorem tReg_nlow (k : Nat) : tReg k ∉ [VReg.v2, .v3, .v4] := by unfold tReg; split <;> decide
theorem sReg_nlow (k : Nat) : sReg k ∉ [VReg.v2, .v3, .v4] := by unfold sReg; split <;> decide

/-- The powers stored. -/
theorem sws_ok {s₀ : State} {H : Block} (hI : PT H 8 s₀)
    (hw : InRegions s₀.wr (s₀.gpr .x19 + BitVec.ofNat 64 512) 192) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun k => [.strq (sReg (k + 1)) .x19 (sOff (k + 1))]))
      s₀ (TS s₀ H n 0) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, nofun, nofun⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s h => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have e := sOff_eq n
    refine WP.mono (st_ok (s := s) (sReg (n + 1)) (d := sOff (n + 1)) (by omega) (by omega) (by omega)
      (by rw [h.wr, h.gpr]; exact hw)) fun s' ⟨hs', f'⟩ => ?_
    subst hs'
    refine ⟨h.v, h.gpr, h.sp, h.rd, h.wr, h.frame.trans (h.gpr ▸ f'), fun k hk => ?_, nofun⟩
    dsimp only
    rw [h.gpr]
    rcases (by omega : k = n ∨ k < n) with rfl | hk'
    · rw [readW_write_self, h.v _ (sReg_nlow _), hI.sw _ (by omega) (by omega)]
    · rw [readW_write_sep (by rw [sOff_eq, sOff_eq]; omega) (by rw [sOff_eq]; omega) (by omega), h.sw k hk']

theorem kpack_eq (a b : BitVec 128) :
    ext8 (ext8 a a ^^^ a) (ext8 b b ^^^ b) = ofVDwords (kkey (ext8 a a)) (kkey (ext8 b b)) := by
  rw [ext8_eq, ofVDwords, kkey, kkey, vdword_xor, vdword_xor, vdword_ext8_0, vdword_ext8_1, vdword_ext8_0,
    vdword_ext8_1, BitVec.xor_comm (vdword a 0)]

theorem nlow {r : VReg} (hr : r ∉ [VReg.v2, .v3, .v4]) : r ≠ .v2 ∧ r ≠ .v3 ∧ r ≠ .v4 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr

/-- A pair's keys computed. -/
theorem kv_ok (k l : Nat) (s : State) :
    WP isa (.block [.vop (.logic .eor .v2 (sReg k) (tReg k)), .vop (.logic .eor .v3 (sReg l) (tReg l)),
      .vop (.ext .v4 .v2 .v3 8)]) s fun s' =>
      s'.v .v4 = ext8 (s.v (sReg k) ^^^ s.v (tReg k)) (s.v (sReg l) ^^^ s.v (tReg l)) ∧
      (∀ r, r ∉ [VReg.v2, .v3, .v4] → s'.v r = s.v r) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [WP.block_cons_iff]
  refine ⟨_, exec_eor _ _ _ _, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_eor _ _ _ _, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_ext8 _ _ _ _, WP.block_nil ⟨?_, fun r hr => ?_, by simp only [gpr_setV],
    by simp only [mem_setV], by simp only [sp_setV], by simp only [rd_setV], by simp only [wr_setV]⟩⟩
  · rw [v_setV_self, v_setV_self, v_setV_of_ne _ _ (by decide), v_setV_self,
      v_setV_of_ne _ _ (nlow (sReg_nlow l)).1, v_setV_of_ne _ _ (nlow (tReg_nlow l)).1]
  · rw [v_setV_of_ne _ _ (nlow hr).2.2, v_setV_of_ne _ _ (nlow hr).2.1, v_setV_of_ne _ _ (nlow hr).1]

/-- A pair of keys stored. -/
theorem key_ok {s₀ : State} {H : Block} (hI : PT H 8 s₀)
    (hw : InRegions s₀.wr (s₀.gpr .x19 + BitVec.ofNat 64 512) 192) {q : Nat} (hq : q < 4) {s : State}
    (h : TS s₀ H 8 q s) :
    WP isa (.block [.vop (.logic .eor .v2 (sReg (pk q)) (tReg (pk q))),
      .vop (.logic .eor .v3 (sReg (pl q)) (tReg (pl q))),
      .vop (.ext .v4 .v2 .v3 8), .strq .v4 .x19 (kOff q)]) s (TS s₀ H 8 (q + 1)) := by
  obtain ⟨k1, k8, l1, l8⟩ := pkl_range q hq
  have e := kOff_eq q
  rw [show ∀ a b c d : Instr, [a, b, c, d] = [a, b, c] ++ [d] from fun _ _ _ _ => rfl, WP.block_append_iff]
  refine WP.mono (kv_ok (pk q) (pl q) s) fun s₃ ⟨v4, v₃, g₃, m₃, sp₃, rd₃, wr₃⟩ => ?_
  refine WP.mono (st_ok .v4 (d := kOff q) (by omega) (by omega) (by omega)
    (by rw [wr₃, g₃, h.wr, h.gpr]; exact hw)) fun s' ⟨hs', f'⟩ => ?_
  subst hs'
  refine ⟨fun r hr => by dsimp only; rw [v₃ r hr, h.v r hr], by dsimp only; rw [g₃, h.gpr],
    by dsimp only; rw [sp₃, h.sp], by dsimp only; rw [rd₃, h.rd], by dsimp only; rw [wr₃, h.wr],
    h.frame.trans (by rw [← m₃]; rw [show tblR (s₃.gpr .x19) = tblR (s₀.gpr .x19) by rw [g₃, h.gpr]] at f'; exact f'), fun k hk => ?_, fun p hp => ?_⟩
  · dsimp only
    rw [g₃, m₃, h.gpr, readW_write_sep (by rw [sOff_eq, kOff_eq]; omega) (by rw [sOff_eq]; omega) (by omega),
      h.sw k hk]
  · dsimp only
    rw [g₃, m₃, h.gpr]
    rcases (by omega : p = q ∨ p < q) with rfl | hp'
    · rw [readW_write_self, v4, h.v _ (sReg_nlow _), h.v _ (tReg_nlow _), h.v _ (sReg_nlow _),
        h.v _ (tReg_nlow _), hI.sw _ k1 k8, hI.t _ k1 k8, hI.sw _ l1 l8, hI.t _ l1 l8, kpack_eq]
      rfl
    · rw [readW_write_sep (by rw [kOff_eq, kOff_eq]; omega) (by rw [kOff_eq]; omega) (by omega), h.key p hp']

/-- The table of keys: the powers with their halves swapped, and the pairs' keys. -/
theorem tbl_ok {s₀ : State} {H : Block} (hI : PT H 8 s₀)
    (hw : InRegions s₀.wr (s₀.gpr .x19 + BitVec.ofNat 64 512) 192) :
    WP isa (.block Impl.AesGcm.AArch64.Stitch.tbl) s₀ (TS s₀ H 8 4) := by
  have ks : ∀ q ≤ 4, ∀ s, TS s₀ H 8 0 s → WP isa (.block ((List.range q).flatMap fun p =>
      [.vop (.logic .eor .v2 (sReg (pk p)) (tReg (pk p))), .vop (.logic .eor .v3 (sReg (pl p)) (tReg (pl p))),
       .vop (.ext .v4 .v2 .v3 8), .strq .v4 .x19 (kOff p)])) s (TS s₀ H 8 q) := by
    intro q hq s h
    induction q with
    | zero => exact WP.block_nil ⟨h.v, h.gpr, h.sp, h.rd, h.wr, h.frame, h.sw, nofun⟩
    | succ q ih =>
      rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
      refine WP.mono (ih (by omega)) fun s' h' => ?_
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact key_ok hI hw (by omega) h'
  rw [Impl.AesGcm.AArch64.Stitch.tbl, WP.block_append_iff]
  exact WP.mono (sws_ok hI hw 8 (Nat.le_refl _)) fun s h => ks 4 (by decide) s h

/-- What the table stores is `Stitch.TblOk`. -/
theorem TS.tblOk {s₀ s : State} {H : Block} (h : TS s₀ H 8 4 s) : TblOk s.mem (s₀.gpr .x19) H :=
  ⟨fun k hk hk8 => by
    have := h.sw (k - 1) (by omega)
    rwa [show k - 1 + 1 = k by omega] at this, h.key⟩

/-! ## The powers from `pw` -/

theorem pwOff_mod16 (k : Nat) : Impl.Gcm.AArch64.Pmull.pwOff k % 16 = 0 := by
  unfold Impl.Gcm.AArch64.Pmull.pwOff; split <;> omega

/-- The power `H'ᵏ` in a buffer of `Powers8Repr`. -/
theorem read_pw {m : Mem} {pw : Addr} {H : Block} (h : Spec.Gcm.Powers8Repr m pw H) {k : Nat} (hk : 1 ≤ k)
    (hk8 : k ≤ 8) : m.read (pw + BitVec.ofNat 64 (Impl.Gcm.AArch64.Pmull.pwOff k)) 16 = pp H k := by
  have hr : ∀ a v, m.readW a 128 = v → m.read a 16 = v := fun a v h => by
    rw [← h]; show _ = BitVec.setWidth 128 (m.read a 16); rw [BitVec.setWidth_eq]
  obtain ⟨j, hj | hj⟩ : ∃ j, k = 2 * j + 2 ∨ k = 2 * j + 1 := ⟨(k - 1) / 2, by omega⟩
  · subst hj
    rw [show Impl.Gcm.AArch64.Pmull.pwOff (2 * j + 2) = 32 * j by
      unfold Impl.Gcm.AArch64.Pmull.pwOff; rw [ite_eq_left (by omega)]; omega]
    exact hr _ _ (h j (by omega)).1
  · subst hj
    rw [show Impl.Gcm.AArch64.Pmull.pwOff (2 * j + 1) = 16 + 32 * j by
      unfold Impl.Gcm.AArch64.Pmull.pwOff; rw [ite_eq_right (by omega)]; omega]
    exact hr _ _ (h j (by omega)).2

/-- `H'ᵏ` loaded from `x5 + pwOff k`, its halves swapped. -/
theorem loadPw_ok' (k : Nat) (s : State) (hin : InRegions (s.rd ++ s.wr)
    (s.gpr .x5 + BitVec.ofNat 64 (Impl.Gcm.AArch64.Pmull.pwOff k)) 16) (hk : k ≤ 8) :
    WP isa (.block (Impl.Gcm.AArch64.Pmull.loadPw k)) s fun s' =>
      s'.v (tReg k) = s.mem.read (s.gpr .x5 + BitVec.ofNat 64 (Impl.Gcm.AArch64.Pmull.pwOff k)) 16 ∧
      s'.v (sReg k) = ext8 (s'.v (tReg k)) (s'.v (tReg k)) ∧ VOnly [tReg k, sReg k] s s' := by
  have ho' : Impl.Gcm.AArch64.Pmull.pwOff k < 4096 * 16 := by unfold Impl.Gcm.AArch64.Pmull.pwOff; split <;> omega
  refine WP.block_cons_iff.mpr ⟨_, Proof.Gcm.AArch64.Pmull.exec_ldrq (pwOff_mod16 k) ho' hin, ?_⟩
  refine WP.mono (swap_ok (sReg k) (tReg k) _) fun s' ⟨w, o⟩ => ?_
  have ts : tReg k ∉ [sReg k] := by
    simp only [List.mem_singleton]; exact tReg_ne_sReg _ _
  refine ⟨by rw [o.v _ ts, v_setV_self], by rw [w, o.v _ ts], ⟨fun r hr => ?_, o.gpr, o.mem, o.rd, o.wr, o.sp⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [o.v r (by simp only [List.mem_singleton]; exact hr.2), v_setV_of_ne _ _ hr.1]

/-- The powers loaded from a buffer `pw` of `Powers8Repr` at `x5`. -/
theorem loadPws_ok {H : Block} {u : State} (hP : Spec.Gcm.Powers8Repr u.mem (u.gpr .x5) H)
    (hin : ∀ k, 1 ≤ k → k ≤ 8 → InRegions (u.rd ++ u.wr)
      (u.gpr .x5 + BitVec.ofNat 64 (Impl.Gcm.AArch64.Pmull.pwOff k)) 16) :
    ∀ K ≤ 8, WP isa (.block ((List.range K).flatMap fun k => Impl.Gcm.AArch64.Pmull.loadPw (k + 1))) u
      fun s => PT H K s ∧ s.gpr = u.gpr ∧ s.mem = u.mem ∧ s.rd = u.rd ∧ s.wr = u.wr ∧ s.sp = u.sp := by
  intro K hK
  induction K with
  | zero => exact WP.block_nil ⟨⟨fun _ h1 h2 => absurd h2 (by omega), fun _ h1 h2 => absurd h2 (by omega)⟩, rfl, rfl,
      rfl, rfl, rfl⟩
  | succ K ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s hs => ?_
    obtain ⟨h, g, m, rd, wr, sp⟩ := hs
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (loadPw_ok' (K + 1) s (by rw [rd, wr, g]; exact hin _ (by omega) (by omega)) hK)
      fun s' hs' => ?_
    obtain ⟨t, w, o⟩ := hs'
    have kv : ∀ r, r ≠ tReg (K + 1) → r ≠ sReg (K + 1) → s'.v r = s.v r := fun r h1 h2 =>
      o.v r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h2⟩)
    have ht' : s'.v (tReg (K + 1)) = pp H (K + 1) := by rw [t, g, m]; exact read_pw hP (by omega) hK
    refine ⟨⟨fun k hk hkK => ?_, fun k hk hkK => ?_⟩, by rw [o.gpr, g], by rw [o.mem, m], by rw [o.rd, rd],
      by rw [o.wr, wr], by rw [o.sp, sp]⟩
    · rcases (by omega : k = K + 1 ∨ k ≤ K) with rfl | hkK'
      · exact ht'
      · rw [kv _ (fun e => by have := tReg_inj k (by omega) (K + 1) (by omega) hk (by omega) e; omega)
          (tReg_ne_sReg _ _), h.t k hk hkK']
    · rcases (by omega : k = K + 1 ∨ k ≤ K) with rfl | hkK'
      · rw [w, ht']
      · rw [kv _ (fun e => tReg_ne_sReg _ _ e.symm)
          (fun e => by have := sReg_inj k (by omega) (K + 1) (by omega) hk (by omega) e; omega), h.sw k hk hkK']

end VG.Proof.AesGcm.AArch64.Stitch
