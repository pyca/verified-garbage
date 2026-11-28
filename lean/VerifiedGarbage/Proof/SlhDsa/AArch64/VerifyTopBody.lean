module

-- separate module: the comparison and the whole body, which the constant-time proof does not need

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyTopLoop
import VerifiedGarbage.Proof.Bignum.ByteDigits
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SLH-DSA (SHAKE) on AArch64, `verify`: the body

The comparison of the last root with `PK.root`, without a branch, and the
epilogue (`tail_ok`); then the body as a whole (`body_ok`), from the entry
state: `BodyPost`, 1 if the root is `PK.root` and 0 if not (`vOk`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.VerifyTop

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.X86_64.VerifyTop (VPar)
open VG.Proof.SlhDsa.AArch64.Sign (untouched)
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_addImm wp_movz wp_ldrx wp_eor wp_orr wp_sub wp_lsr)

/-! ## Words and bytes -/

theorem bytes8_eq (m : Mem) (A B : Addr) : bytesAt m A 8 = bytesAt m B 8 ↔ m.readW A 64 = m.readW B 64 := by
  constructor
  · intro h
    apply Proof.Bignum.ByteDigits.eq_of_bytes
    intro j hj
    rw [Blocks.byte_readW64 m A hj, Blocks.byte_readW64 m B hj]
    have := congrArg (fun l : List Byte => l[j]?) h
    simpa [bytesAt, hj] using this
  · intro h
    simp only [bytesAt]
    refine List.map_congr_left fun j hj => ?_
    have hj' := List.mem_range.mp hj
    rw [← Blocks.byte_readW64 m A hj', ← Blocks.byte_readW64 m B hj', h]

theorem bytes_eq_words (m : Mem) (A B : Addr) : ∀ w, bytesAt m A (8 * w) = bytesAt m B (8 * w) ↔
    ∀ i < w, m.readW (A + BitVec.ofNat 64 (8 * i)) 64 = m.readW (B + BitVec.ofNat 64 (8 * i)) 64
  | 0 => by simp [bytesAt]
  | w + 1 => by
    rw [show 8 * (w + 1) = 8 * w + 8 by omega, KeyGen.bytesAt_add', KeyGen.bytesAt_add']
    have iff : bytesAt m A (8 * w) ++ bytesAt m (A + BitVec.ofNat 64 (8 * w)) 8 =
        bytesAt m B (8 * w) ++ bytesAt m (B + BitVec.ofNat 64 (8 * w)) 8 ↔
        bytesAt m A (8 * w) = bytesAt m B (8 * w) ∧
          bytesAt m (A + BitVec.ofNat 64 (8 * w)) 8 = bytesAt m (B + BitVec.ofNat 64 (8 * w)) 8 :=
      ⟨fun h => List.append_inj h (by rw [bytesAt_len, bytesAt_len]), fun ⟨h1, h2⟩ => by rw [h1, h2]⟩
    rw [iff, bytes_eq_words m A B w, bytes8_eq]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h1 i hi
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h w (by omega)⟩

theorem nz_bit (x : BitVec 64) : ((0 - x) ||| x) >>> 63 = if x = 0 then 0 else 1 := by
  by_cases h : x = 0
  · subst h; rfl
  · simp only [h, ↓reduceIte]
    obtain hx : x.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq h')
    have hlt := x.isLt
    obtain hneg : (0 - x).toNat = 2 ^ 64 - x.toNat := by
      rw [BitVec.toNat_sub, show (0 : BitVec 64).toNat = 0 from rfl]; omega
    obtain h1 : 2 ^ 63 ≤ ((0 - x) ||| x).toNat := by
      rw [BitVec.toNat_or]
      rcases Nat.lt_or_ge x.toNat (2 ^ 63) with h2 | h2
      · exact Nat.le_trans (by omega) (Nat.left_le_or (m := x.toNat))
      · exact Nat.le_trans h2 Nat.right_le_or
    obtain h2 := ((0 - x) ||| x).isLt
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, show (1 : BitVec 64).toNat = 1 from rfl]
    omega

theorem or_xor_zero (a b c : BitVec 64) : (a ||| (b ^^^ c)) = 0 ↔ a = 0 ∧ b = c := by
  rw [← BitVec.xor_eq_zero_iff (x := b)]
  exact BitVec.or_eq_zero_iff

/-! ## The comparison and the epilogue -/

/-- After `w` words of the comparison. -/
def CI (S : Addr) (t : State) (w : Nat) (u : State) : Prop :=
  Only [.x9, .x10, .x11] t u ∧ (u.gpr .x9 = 0 ↔
    ∀ i < w, t.mem.readW (at' S Layout.oMsg + BitVec.ofNat 64 (8 * i)) 64 =
      t.mem.readW (at' S Layout.oPkRoot + BitVec.ofNat 64 (8 * i)) 64)

theorem cmp_ok {p : Params} (hz : Sz p) {σ t : State} (hK : VG p σ) (hc : Ctx p σ t) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ u, Only [.x9, .x10, .x11] t u → u.gpr .x9 = (if bytesAt t.mem (at' (σ.gpr .x7) Layout.oMsg) p.n =
        bytesAt t.mem (at' (σ.gpr .x7) Layout.oPkRoot) p.n then 1 else 0) → WP isa (.block is) u Q) :
    WP isa (.block (Impl.SlhDsa.AArch64.Verify.compareRoot p ++ is)) t Q := by
  have hn := hz.n32
  have h8 := hz.n8
  have hw : (⟨σ.gpr .x7, scratchLen⟩ : Region) ∈ t.rd ++ t.wr := by
    rw [hc.wr, hK.wr]; exact List.mem_append_right _ (by simp)
  unfold Impl.SlhDsa.AArch64.Verify.compareRoot
  simp only [List.cons_append, List.append_assoc]
  refine wp_movz fun t₀ o₀ e₀ => ?_
  refine KeyGen.wp_flatMap (P := CI (σ.gpr .x7) t) (p.n / 8)
    ⟨o₀.mono (by decide), by rw [e₀]; exact ⟨fun _ _ h => absurd h (by omega), fun _ => rfl⟩⟩
    (fun w hw' u is' ⟨hu, hz9⟩ k' => ?_) fun u ⟨hu, hz9⟩ => ?_
  · have hin : ∀ {o : Nat}, o + 8 ≤ scratchLen → InRegions (u.rd ++ u.wr) (σ.gpr .x7 + BitVec.ofNat 64 o) 8 :=
      fun h => by rw [hu.rd, hu.wr]; exact KeyGen.in_scr hw h
    have h19 : u.gpr .x19 = σ.gpr .x7 := by rw [hu.get .x19, hc.x19]
    simp only [List.cons_append, List.nil_append]
    refine wp_ldrx (a := at' (σ.gpr .x7) (Layout.oMsg + 8 * w))
      ⟨by simp only [Layout.oMsg]; omega, by simp only [Layout.oMsg]; omega⟩ (by rw [h19])
      (hin (by simp only [Layout.oMsg, scratchLen]; omega)) fun u₁ o₁ e₁ => ?_
    refine wp_ldrx (a := at' (σ.gpr .x7) (Layout.oPkRoot + 8 * w))
      ⟨by simp only [Layout.oPkRoot, Layout.oKeys]; omega, by simp only [Layout.oPkRoot, Layout.oKeys]; omega⟩
      (by rw [o₁.get .x19, h19]) (by rw [o₁.rd, o₁.wr]; exact hin (by simp only [Layout.oPkRoot, Layout.oKeys, scratchLen]; omega))
      fun u₂ o₂ e₂ => wp_eor fun u₃ o₃ e₃ => wp_orr fun u₄ o₄ e₄ => k' u₄ ⟨?_, ?_⟩
    · exact ((((hu.trans o₁).trans o₂).trans o₃).trans o₄).mono (by decide)
    · rw [e₄, o₃.get .x9, o₂.get .x9, o₁.get .x9, e₃, o₂.get .x10, e₁, e₂, o₁.mem, hu.mem]
      rw [or_xor_zero, hz9]
      simp only [at']
      rw [← addr_add, ← addr_add]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact h1 i hi
        · exact h2
      · intro h
        exact ⟨fun i hi => h i (by omega), h w (by omega)⟩
  · refine wp_movz fun u₁ o₁ e₁ => wp_sub fun u₂ o₂ e₂ => wp_orr fun u₃ o₃ e₃ => wp_lsr (by decide)
      fun u₄ o₄ e₄ => wp_movz fun u₅ o₅ e₅ => wp_sub fun u₆ o₆ e₆ => k u₆ ?_ ?_
    · exact ((((((hu.trans o₁).trans o₂).trans o₃).trans o₄).trans o₅).trans o₆).mono (by decide)
    · have e8 : 8 * (p.n / 8) = p.n := by omega
      have hw' := bytes_eq_words t.mem (at' (σ.gpr .x7) Layout.oMsg) (at' (σ.gpr .x7) Layout.oPkRoot) (p.n / 8)
      rw [e8] at hw'
      rw [e₆, e₅, o₅.get .x10, e₄, e₃, o₂.get .x9, e₂, e₁, o₁.get .x9,
        show BitVec.setWidth 64 (0 : BitVec 16) = 0 from rfl, show BitVec.setWidth 64 (1 : BitVec 16) = 1 from rfl,
        nz_bit]
      by_cases hb : bytesAt t.mem (at' (σ.gpr .x7) Layout.oMsg) p.n = bytesAt t.mem (at' (σ.gpr .x7) Layout.oPkRoot) p.n
      · have h0 : u.gpr .x9 = 0 := hz9.mpr (hw'.mp hb)
        simp only [hb, h0, ↓reduceIte]; rfl
      · have h0 : u.gpr .x9 ≠ 0 := fun h => hb (hw'.mpr (hz9.mp h))
        simp only [hb, h0, ↓reduceIte]; rfl

/-- The comparison and the epilogue: the caller's registers back, and the result. -/
theorem tail_ok {p : Params} (hz : Sz p) {σ t : State} (hK : VG p σ) (hc : Ctx p σ t) :
    WP isa (.block (Impl.SlhDsa.AArch64.Verify.compareRoot p ++
      Impl.SlhDsa.AArch64.restoreRegsAt Layout.oTop Impl.SlhDsa.AArch64.Shake.topSaved ++
      [Impl.SlhDsa.AArch64.Thash4.mov .x0 .x9])) t fun w =>
      abiPreserved σ w ∧ w.gpr .x0 = (if bytesAt t.mem (at' (σ.gpr .x7) Layout.oMsg) p.n =
        bytesAt t.mem (at' (σ.gpr .x7) Layout.oPkRoot) p.n then 1 else 0) := by
  have hw : (⟨σ.gpr .x7, scratchLen⟩ : Region) ∈ t.wr := by rw [hc.wr, hK.wr]; simp
  rw [List.append_assoc]
  refine cmp_ok hz hK hc fun u o e => ?_
  refine restoreRegsAt_ok KeyGen.topSaved_nodup ⟨by decide, by decide⟩
    (by rw [o.get .x19, hc.x19, o.rd, o.wr]; exact KeyGen.in_scr (List.mem_append_right _ hw) (by decide))
    fun u' o' v => ?_
  refine wp_addImm (by decide) fun w o'' e'' => wp_nil ⟨⟨fun r hr => ?_, by rw [o''.sp, o'.sp, o.sp, hc.sp],
    fun r hr => by rw [o''.vcs r hr, o'.vcs r hr, o.vcs r hr, hc.vcs r hr]⟩, ?_⟩
  · rw [o''.get r (by revert r; decide)]
    by_cases h : r ∈ Impl.SlhDsa.AArch64.Shake.topSaved
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
      rw [v i hi, o.get .x19, hc.x19, o.mem,
        hc.saved i (by simp only [Impl.SlhDsa.AArch64.Shake.topSaved, List.length] at hi; omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    · have hu : r ∈ untouched := by revert r h; decide
      rw [o'.get r (by revert r hu; decide), o.get r (by revert r hu; decide), hc.cs r hu]
  · rw [e'', BitVec.add_zero, o'.get .x9, e]

/-! ## The body -/

theorem verifyBody_eq (p : Params) (f : Impl.SlhDsa.AArch64.Shake.Fns) (g : Impl.SlhDsa.AArch64.Verify.VFns) :
    Impl.SlhDsa.AArch64.Verify.verifyBody p f g =
      .seq (.block (proCode p))
        (.seq (Impl.SlhDsa.AArch64.Shake.hashM' p f [.reg .x24, .scr Layout.oPkSeed, .scr Layout.oPkRoot]
          (.scr Layout.oDigest) p.m)
          (.seq (.block (fblock p))
            (.seq (.call g.forsPkName (Impl.SlhDsa.AArch64.Verify.forsPk p f))
              (.seq (.block (([.movz .x .x21 0 0] : List Instr) ++ Impl.SlhDsa.AArch64.lea .x20 .x24 (p.n + p.forsSigLen)))
                (.seq (.loop (Impl.SlhDsa.AArch64.Verify.layerBody p f g) (.nonzero .x .x9))
                  (.block (Impl.SlhDsa.AArch64.Verify.compareRoot p ++
                    Impl.SlhDsa.AArch64.restoreRegsAt Layout.oTop Impl.SlhDsa.AArch64.Shake.topSaved ++
                    [Impl.SlhDsa.AArch64.Thash4.mov .x0 .x9]))))))) := by
  simp only [Impl.SlhDsa.AArch64.Verify.verifyBody, proCode, fblock, List.append_assoc, List.cons_append,
    List.nil_append]

/-- The body of `verify`, for any `thash4` (`T`). -/
theorem body_ok {p : Params} (hp : VPar p) (hh : p.hp = 3 ∨ p.hp = 4 ∨ p.hp = 8 ∨ p.hp = 9)
    {f : Impl.SlhDsa.AArch64.Shake.Fns} (v : Proof.Sha3.AArch64.Permutation) (hv : f.keccak = v.callee)
    (T : Thash4Impl p.n) (ht : f.t4 = T.code) (g : Impl.SlhDsa.AArch64.Verify.VFns)
    {σ s : State} (hK : VG p σ) (hsl : (σ.gpr .x6).toNat = p.sigLen) (hs : Only [.x9, .x10] σ s) :
    WP isa (Impl.SlhDsa.AArch64.Verify.verifyBody p f g) s (BodyPost p σ) := by
  have hz := Sz.of_vpar hp
  rw [verifyBody_eq]
  refine WP.seq (WP.mono (pro_ok hz hK hs) fun t₁ ⟨c₁, r₁⟩ => ?_)
  refine WP.seq (WP.mono (hash_ok hz hp.m64 v hv hK hsl c₁ r₁) fun t₂ ⟨c₂, D₂⟩ => ?_)
  refine WP.seq (WP.mono (fblock_ok hp hK c₂ D₂) fun u hu => ?_)
  refine WP.seq (WP.mono (fors_ok hp T ht g.forsPkName hK hsl hu) fun s' hs' => ?_)
  refine WP.seq (WP.mono (init_wp hp hK hs') fun w hw => ?_)
  refine WP.seq (WP.mono (loop_ok hp hh T ht g hK hsl hw) fun t₄ h₄ => ?_)
  refine WP.mono (tail_ok hz hK h₄.ctx) fun w ⟨habi, hret⟩ => ⟨habi, ?_⟩
  have hk1 := h₄.ctx.keys 1 (by decide)
  simp only [Nat.mul_one] at hk1
  rw [show Layout.oPkSeed + 32 = Layout.oPkRoot from rfl] at hk1
  rw [hret, h₄.msg, hk1]
  by_cases e : (htV p σ p.d).1 = PKr p σ
  · simp only [vOk, e, beq_self_eq_true, ↓reduceIte]; rfl
  · simp only [vOk, e, ↓reduceIte, beq_iff_eq]; rfl

/-- `verify` meets `vgK`, for any `thash4` (`T`). -/
theorem verify_correct {p : Params} (hp : VPar p) (hh : p.hp = 3 ∨ p.hp = 4 ∨ p.hp = 8 ∨ p.hp = 9)
    {f : Impl.SlhDsa.AArch64.Shake.Fns} (v : Proof.Sha3.AArch64.Permutation) (hv : f.keccak = v.callee)
    (T : Thash4Impl p.n) (ht : f.t4 = T.code) (g : Impl.SlhDsa.AArch64.Verify.VFns) :
    ∀ s, (vgK p).pre s → ∃ t s', Exec isa (Impl.SlhDsa.AArch64.Verify.verify p f g) s t s' ∧
      abiPreserved s s' ∧ (vgK p).post s s' := fun _ h => by
  obtain ⟨t, s', e, hq⟩ := verify_wp hp (fun σ s hK _ h6 hs => body_ok hp hh v hv T ht g hK h6 hs) h
  exact ⟨t, s', e, hq.1, hq.2⟩

end VG.Proof.SlhDsa.AArch64.VerifyTop
