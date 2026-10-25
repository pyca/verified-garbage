module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.EncPre
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.EncLoops
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Callee
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-!
# `vg_rsa_pkcs1_encrypt_precomputed` on PPC64LE: up to the call

`setup_ok`: the saves, `out`, `k`, `e` and `e_len` kept in `r28`–`r31`, and
`EM`'s first two bytes (`Setup`). `em_ok`: `PS`, the separator and `M`
complete `EM = encode M PS` (`EmDone`), with `PS`'s zero test in `r5`.
`callArgs_ok` and `call_ok`: the call writes RSAEP of `EM` to `out` if `pre`
holds the modulus' values (`AfterCall`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Enc

open VG VG.PPC64LE VG.Impl.RsaPkcs1Sig.PPC64LE VG.Impl.RsaPkcs1Enc.PPC64LE.Precomputed VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.PPC64LE
open VG.Proof.RsaPkcs1Sig (bytesAt_length frame_writeBytes)

/-- In the frame: `out`, `k`, `e` and `e_len` kept. -/
abbrev EMid (s t : State) : Prop := Mid (scR s) s (s.gpr .r3) (s.gpr .r6) (s.gpr .r7) (s.gpr .r8) t

/-- `EM`'s place. -/
abbrev emA (s : State) : Addr := fb s + BitVec.ofNat 64 oEM

/-- `EM` holds `xs` over some memory `M₀`. -/
def Em (s : State) (xs : List Byte) (t : State) : Prop := ∃ M₀ : Mem, t.mem = writeBytes M₀ (emA s) xs

section
variable {s : State}

theorem in_a6R {j : Nat} (hj : j < 6) : (a6R s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)

theorem arg_rd (hp : PreE s) (rs : List Region) {j : Nat} (hj : j < 6) :
    InRegions (s.rd ++ rs) (stackArgAddr s j) 8 :=
  ⟨a6R s, List.mem_append_left _ (by rw [hp.hrd]; simp), in_a6R hj⟩

theorem arg_frame (hp : PreE s) {m : Mem} (h : Frame [kR s] s.mem m) {j : Nat} (hj : j < 6) :
    m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (in_a6R hj) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.ka.symm) (by decide)

/-- A stack argument, in memory changed only in the frame and the working
space. -/
theorem arg_mid (hp : PreE s) {m : Mem} (h : Frame [kR s, scR s] s.mem m) {j : Nat} (hj : j < 6) :
    m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (in_a6R hj) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.ka.symm
    · exact hp.sa.symm) (by decide)

end

theorem add_ofNat_ofNat (a : Addr) (d e : Nat) :
    a + BitVec.ofNat 64 d + BitVec.ofNat 64 e = a + BitVec.ofNat 64 (d + e) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- After the setup. -/
structure Setup (s w : State) : Prop extends
    Mid (scR s) s (s.gpr .r3) (s.gpr .r6) (s.gpr .r7) (s.gpr .r8) w where
  em : Em s [0x00, 0x02] w
  g4 : w.gpr .r4 = stackArg s 0
  g5 : w.gpr .r5 = 0
  g9 : w.gpr .r9 = s.gpr .r9
  g10 : w.gpr .r10 = s.gpr .r10
  g11 : w.gpr .r11 = fb s + BitVec.ofNat 64 (oEM + 2)
  g12 : w.gpr .r12 = stackArg s 1

theorem setup_ok {s u : State} (hp : PreE s) (hsp : u.sp = fb s) (hwr : u.wr = fr s :: s.wr)
    (hrd : u.rd = s.rd) (hm : Frame [kR s] s.mem u.mem) (hg : ∀ r, r ∉ [Reg.r11, .r12] → u.gpr r = s.gpr r)
    (hlr : u.lr = s.lr) :
    WP isa (.block setup) u (Setup s) := by
  unfold setup
  refine save_ok hsp hwr hm (fun r hr => hg r (by revert r; decide)) hlr fun v kv v12 fv sv lv => ?_
  have gv : ∀ r, r ∉ [Reg.r12, .r0, .r11] → v.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [kv.gpr r (by simp [hr.1, hr.2.1]), hg r (by simp [hr.1, hr.2.2])]
  refine wp_mov fun v₁ o₁ e₁ => wp_mov fun v₂ o₂ e₂ => wp_mov fun v₃ o₃ e₃ => wp_mov fun v₄ o₄ e₄ =>
    wp_li (by decide) fun v₅ o₅ e₅ => ?_
  have O₅ : Only [.r28, .r29, .r30, .r31, .r0] v v₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  have r12₅ : v₅.gpr .r12 = fb s := by rw [O₅.get .r12, v12]
  have wr₅ : v₅.wr = fr s :: s.wr := by rw [O₅.wr, kv.wr, hwr]
  refine wp_stb (a := emA s) (by rw [r12₅]) (by rw [wr₅]; exact in_fr s _ (by decide) (by decide))
    fun v₆ m₆ => wp_li (by decide) fun v₇ o₇ e₇ => ?_
  refine wp_stb (a := emA s + BitVec.ofNat 64 1) (by rw [o₇.get .r12, m₆.gpr, r12₅, add_ofNat_ofNat])
    (by rw [o₇.wr, m₆.wr, wr₅, add_ofNat_ofNat]; exact in_fr s _ (by decide) (by decide)) fun v₈ m₈ => ?_
  have r12₈ : v₈.gpr .r12 = fb s := by rw [m₈.gpr, o₇.get .r12, m₆.gpr, r12₅]
  have rd₈ : v₈.rd = s.rd := by rw [m₈.rd, o₇.rd, m₆.rd, O₅.rd, kv.rd, hrd]
  have mem₈ : v₈.mem = writeBytes v.mem (emA s) [0x00, 0x02] := by
    have b0 : (BitVec.ofNat 64 0).setWidth 8 = (0x00 : Byte) := by decide
    have b2 : (BitVec.ofNat 64 2).setWidth 8 = (0x02 : Byte) := by decide
    rw [m₈.mem, o₇.mem, m₆.mem, O₅.mem, e₇, e₅, b0, b2,
      show ([0x00, 0x02] : List Byte) = [] ++ [0x00] ++ [0x02] from rfl, writeBytes_snoc _ _ _ _ (by decide),
      writeBytes_snoc _ _ _ _ (by decide), writeBytes_nil]
    simp only [List.length_nil, List.nil_append, List.length_singleton, BitVec.add_zero]
  have fr₈ : Frame [kR s] s.mem v₈.mem := by
    rw [mem₈]
    have hw := frame_writeBytes v.mem (emA s) [0x00, 0x02]
    exact fv.trans (hw.sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_singleton_self _, Proof.RsaPkcs1Sig.PPC64LE.frame_sub s (d := oEM) (n := 2) (by decide)⟩)
  have hdS : ∀ {d k : Nat}, d + k ≤ oLr + 8 →
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, k⟩ ⟨emA s, 2⟩ := fun hk =>
    Offset.disjoint _ (.inl (by unfold oLr oEM oEM1 at *; omega_arith)) (by unfold oLr at hk; omega_arith) (by decide)
  refine wp_ld (a := stackArgAddr s 0) (by rw [r12₈, stackArgAddr_fb]) (by rw [rd₈]; exact arg_rd hp _ (by decide))
    fun v₉ o₉ e₉ => wp_addi fun v₁₀ o₁₀ e₁₀ => wp_li (by decide) fun v₁₁ o₁₁ e₁₁ => ?_
  refine wp_ld (a := stackArgAddr s 1) (by rw [o₁₁.get .r12, o₁₀.get .r12, o₉.get .r12, r12₈, stackArgAddr_fb])
    (by rw [o₁₁.rd, o₁₀.rd, o₉.rd, rd₈]; exact arg_rd hp _ (by decide)) fun v₁₂ o₁₂ e₁₂ => wp_nil ?_
  have O₁₂ : Only [.r4, .r11, .r5, .r12] v₈ v₁₂ := (o₉.trans (o₁₀.trans (o₁₁.trans o₁₂))).mono
  have g₈ : ∀ r, r ∉ [Reg.r0] → v₈.gpr r = v₅.gpr r := fun r hr => by rw [m₈.gpr, o₇.gpr r hr, m₆.gpr]
  have mem₁₂ : v₁₂.mem = writeBytes v.mem (emA s) [0x00, 0x02] := by rw [O₁₂.mem, mem₈]
  refine {
    sp := by rw [O₁₂.sp, m₈.sp, o₇.sp, m₆.sp, O₅.sp, kv.sp, hsp]
    rd := by rw [O₁₂.rd, rd₈]
    wr := by rw [O₁₂.wr, m₈.wr, o₇.wr, m₆.wr, wr₅]
    r28 := by
      rw [O₁₂.get .r28, g₈ .r28 (by decide), o₅.get .r28, o₄.get .r28, o₃.get .r28, o₂.get .r28, e₁,
        gv .r3 (by decide)]
    r29 := by
      rw [O₁₂.get .r29, g₈ .r29 (by decide), o₅.get .r29, o₄.get .r29, o₃.get .r29, e₂, o₁.get .r6,
        gv .r6 (by decide)]
    r30 := by
      rw [O₁₂.get .r30, g₈ .r30 (by decide), o₅.get .r30, o₄.get .r30, e₃, o₂.get .r7, o₁.get .r7,
        gv .r7 (by decide)]
    r31 := by
      rw [O₁₂.get .r31, g₈ .r31 (by decide), o₅.get .r31, e₄, o₃.get .r8, o₂.get .r8, o₁.get .r8,
        gv .r8 (by decide)]
    hi := fun r hr => by
      have h₁ : r ∉ [Reg.r4, .r11, .r5, .r12] := by revert r; decide
      have h₂ : r ∉ [Reg.r0] := by revert r; decide
      have h₃ : r ∉ [Reg.r28, .r29, .r30, .r31, .r0] := by revert r; decide
      have h₄ : r ∉ [Reg.r12, .r0, .r11] := by revert r; decide
      rw [O₁₂.gpr r h₁, g₈ r h₂, O₅.gpr r h₃, gv r h₄]
    mem := by
      rw [O₁₂.mem]
      exact fr₈.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..
    sv := by
      rw [mem₁₂]
      exact sv.frame (frame_writeBytes v.mem (emA s) [0x00, 0x02]) fun p hp r hr => by
        rw [List.mem_singleton.mp hr]; exact hdS (by have := saved_offs p hp; unfold oSave oLr at *; omega_arith)
    ls := by
      rw [mem₁₂, (frame_writeBytes v.mem (emA s) [0x00, 0x02]).readW (Region.contains_self _ _)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hdS (by decide)) (by decide)]
      exact lv
    em := ⟨v.mem, mem₁₂⟩
    g4 := by rw [o₁₂.get .r4, o₁₁.get .r4, o₁₀.get .r4, e₉, arg_frame hp fr₈ (by decide)]
    g5 := by rw [o₁₂.get .r5, e₁₁]; rfl
    g9 := by rw [O₁₂.get .r9, g₈ .r9 (by decide), O₅.get .r9, gv .r9 (by decide)]
    g10 := by rw [O₁₂.get .r10, g₈ .r10 (by decide), O₅.get .r10, gv .r10 (by decide)]
    g11 := by rw [o₁₂.get .r11, o₁₁.get .r11, e₁₀, o₉.get .r12, r12₈]
    g12 := by rw [e₁₂, o₁₁.mem, o₁₀.mem, o₉.mem, arg_frame hp fr₈ (by decide)] }

/-- `M` and `PS`, from the entry state. -/
abbrev msgB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat
abbrev psB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat

/-- `EM` complete, `PS`'s zero test in `r5`, `r12` the frame's base. -/
structure EmDone (s y : State) : Prop extends EMid s y where
  em : Em s (Spec.RsaPkcs1Enc.encode (msgB s) (psB s)) y
  g5 : y.gpr .r5 = zbit (psB s)
  g12 : y.gpr .r12 = fb s

theorem em_ok {s w : State} (hp : PreE s) (hs : Setup s w) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ y, EmDone s y → WP isa rest y Q) :
    WP isa (.seq psLoop (.seq (.block sep) (.seq msgCopy rest))) w Q := by
  have hk1 := hp.k1; have hk2 := hp.k2; have hml := hp.ml; have hpl := hp.pl
  obtain ⟨M₀, hM₀⟩ := hs.em
  have hn : 0 < (stackArg s 1).toNat := by omega_arith
  have hdP : (psR s).Disjoint ⟨emA s + BitVec.ofNat 64 2, (stackArg s 1).toNat⟩ := by
    rw [add_ofNat_ofNat]
    exact (hp.kps.sub_left (Proof.RsaPkcs1Sig.PPC64LE.frame_sub s (d := oEM + 2) (n := (stackArg s 1).toNat)
      (by unfold oEM oEM1 frameBytes; omega_arith))).symm
  refine WP.seq (WP.mono (psLoop_ok (p := emA s + BitVec.ofNat 64 2) (q := stackArg s 0)
    (n := (stackArg s 1).toNat) hn (by omega_arith) hs.g4 (by rw [hs.g11, add_ofNat_ofNat]) (by rw [hs.g12]; simp)
    (fun j hj => ⟨psR s, List.mem_append_left _ (by rw [hs.rd, hp.hrd]; simp),
      Offset.contains_base _ (by omega_arith) (by have := hp.wps; omega_arith)⟩)
    (fun i hi => by
      rw [hs.wr, add_ofNat_ofNat, add_ofNat_ofNat]
      exact in_fr s _ (by unfold oEM oEM1; omega_arith) (by unfold oEM oEM1 frameBytes; omega_arith))
    (fun j hj i hi => Proof.RsaPkcs1Sig.ne_of_disjoint hdP (by omega_arith) (by omega_arith) hj hi))
    fun y₁ ⟨k₁, m₁, r5₁, r11₁⟩ => ?_)
  have hPS : Spec.Rsa.bytesAt w.mem (stackArg s 0) (stackArg s 1).toNat = psB s :=
    bytes_of_frame hs.mem hp.kps hp.pss.symm (by have := hp.wps; omega_arith)
  have hl2 : ([(0x00 : Byte), 0x02] ++ psB s).length = 2 + (stackArg s 1).toNat := by
    simp [bytesAt_length]; omega_arith
  have mem₁ : y₁.mem = writeBytes M₀ (emA s) ([0x00, 0x02] ++ psB s) := by
    rw [m₁, hPS, hM₀, ← writeBytes_append _ _ _ _ (by rw [← List.length_append, hl2]; omega_arith)]
    rfl
  have fr₁ : Frame [⟨fb s + BitVec.ofNat 64 (oEM + 2), (stackArg s 1).toNat⟩] w.mem y₁.mem := by
    have h := frame_writeBytes w.mem (emA s + BitVec.ofNat 64 2)
      (Spec.Rsa.bytesAt w.mem (stackArg s 0) (stackArg s 1).toNat)
    rw [bytesAt_length, add_ofNat_ofNat] at h
    rw [m₁, add_ofNat_ofNat]; exact h
  have mid₁ : EMid s y₁ := hs.toMid.frameW1 k₁ hp.ksc (by decide) (by unfold oEM oEM1 frameBytes; omega_arith) fr₁
  have b0 : (BitVec.ofNat 64 0).setWidth 8 = (0x00 : Byte) := by decide
  have inEM : ∀ {d n : Nat}, d + n ≤ 1024 → InRegions (fr s :: s.wr) (emA s + BitVec.ofNat 64 d) n :=
    fun h => by rw [add_ofNat_ofNat]; exact in_fr s _ (by unfold oEM oEM1; omega_arith) (by unfold oEM oEM1 frameBytes; omega_arith)
  refine WP.seq (wp_li (by decide) fun y₂ o₂ e₂ =>
    wp_stb (a := emA s + BitVec.ofNat 64 (2 + (stackArg s 1).toNat))
      (by rw [o₂.get .r11, r11₁, BitVec.add_zero, add_ofNat_ofNat])
      (by rw [o₂.wr, mid₁.wr]; exact inEM (by omega_arith)) fun y₃ m₃ =>
    wp_addi fun y₄ o₄ e₄ => wp_addSp fun y₅ o₅ e₅ => wp_nil ?_)
  have hl3 : ([(0x00 : Byte), 0x02] ++ psB s ++ [0x00]).length = 3 + (stackArg s 1).toNat := by
    simp [bytesAt_length]; omega_arith
  have mem₃ : y₃.mem = writeBytes M₀ (emA s) ([0x00, 0x02] ++ psB s ++ [0x00]) := by
    rw [writeBytes_snoc _ _ _ _ (by omega_arith), hl2, m₃.mem, o₂.mem, mem₁, e₂, b0]
  have fr₃ : Frame [⟨fb s + BitVec.ofNat 64 (oEM + 2 + (stackArg s 1).toNat), 1⟩] y₁.mem y₃.mem := by
    rw [m₃.mem, o₂.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (by
      rw [add_ofNat_ofNat, show oEM + (2 + (stackArg s 1).toNat) = oEM + 2 + (stackArg s 1).toNat by omega_arith]
      exact Region.contains_self _ _)
  have mid₃ : EMid s y₃ := mid₁.frameW1 (o₂.keep.trans m₃.keep) hp.ksc (by unfold oLr oEM oEM1; omega_arith)
    (by unfold oEM oEM1 frameBytes; omega_arith) fr₃
  have O₅ : Only [.r11, .r12] y₃ y₅ := o₄.trans o₅
  have mid₅ : EMid s y₅ := mid₃.only O₅
  have r12₅ : y₅.gpr .r12 = fb s := by rw [e₅, o₄.sp, m₃.sp, o₂.sp, mid₁.sp, BitVec.add_zero]
  have r11₅ : y₅.gpr .r11 = emA s + BitVec.ofNat 64 (3 + (stackArg s 1).toNat) := by
    rw [o₅.get .r11, e₄, m₃.gpr, o₂.get .r11, r11₁, ofNat_succ', add_ofNat_ofNat,
      show 2 + ((stackArg s 1).toNat + 1) = 3 + (stackArg s 1).toNat by omega_arith]
  have r5₅ : y₅.gpr .r5 = zbit (psB s) := by
    rw [O₅.get .r5, m₃.gpr, o₂.get .r5, r5₁, hs.g5, hPS]; simp
  have r10₅ : y₅.gpr .r10 = s.gpr .r10 := by
    rw [O₅.get .r10, m₃.gpr, o₂.get .r10, k₁.get .r10, hs.g10]
  have r9₅ : y₅.gpr .r9 = s.gpr .r9 := by
    rw [O₅.get .r9, m₃.gpr, o₂.get .r9, k₁.get .r9, hs.g9]
  have mem₅ : y₅.mem = writeBytes M₀ (emA s) ([0x00, 0x02] ++ psB s ++ [0x00]) := by rw [O₅.mem, mem₃]
  refine WP.seq ?_
  unfold msgCopy
  by_cases hm0 : (s.gpr .r10).toNat = 0
  · refine WP.ite false (by rw [eval_nonzero, ne_zero_iff, r10₅, hm0]; rfl) (by simp) fun _ => wp_nil ?_
    refine k y₅ ⟨mid₅, ⟨M₀, ?_⟩, r5₅, r12₅⟩
    rw [mem₅]
    unfold Spec.RsaPkcs1Enc.encode msgB
    rw [hm0]
    simp [Spec.Rsa.bytesAt]
  · refine WP.ite true (by rw [eval_nonzero, ne_zero_iff, r10₅]; simp [hm0]) (fun _ => ?_) (by simp)
    refine WP.seq (wp_mov fun c₁ p₁ f₁ => wp_mov fun c₂ p₂ f₂ => wp_mov fun c₃ p₃ f₃ => wp_nil ?_)
    have P₃ : Only [.r7, .r4, .r8] y₅ c₃ := p₁.trans (p₂.trans p₃)
    have midc : EMid s c₃ := mid₅.only P₃
    have hdM : (mR s).Disjoint ⟨emA s + BitVec.ofNat 64 (3 + (stackArg s 1).toNat), (s.gpr .r10).toNat⟩ := by
      rw [add_ofNat_ofNat]
      exact (hp.km.sub_left (Proof.RsaPkcs1Sig.PPC64LE.frame_sub s (d := oEM + (3 + (stackArg s 1).toNat)) (n := (s.gpr .r10).toNat)
        (by unfold oEM oEM1 frameBytes; omega_arith))).symm
    have hM : Spec.Rsa.bytesAt c₃.mem (s.gpr .r9) (s.gpr .r10).toNat = msgB s :=
      bytes_of_frame midc.mem hp.km hp.ms.symm (by have := hp.wm; omega_arith)
    refine WP.mono (copy_ok (p := emA s + BitVec.ofNat 64 (3 + (stackArg s 1).toNat)) (q := s.gpr .r9)
      (n := (s.gpr .r10).toNat) (by omega_arith) (by omega_arith) (by rw [p₃.get .r4, f₂, p₁.get .r11, r11₅])
      (by rw [p₃.get .r7, p₂.get .r7, f₁, r9₅]) (by rw [f₃, p₂.get .r10, p₁.get .r10, r10₅]; simp)
      (fun j hj => ⟨mR s, List.mem_append_left _ (by rw [midc.rd, hp.hrd]; simp),
        Offset.contains_base _ (by omega_arith) (by have := hp.wm; omega_arith)⟩)
      (fun i hi => by rw [midc.wr, add_ofNat_ofNat]; exact inEM (by omega_arith))
      (fun j hj i hi => Proof.RsaPkcs1Sig.ne_of_disjoint hdM (by omega_arith) (by omega_arith) hj hi))
      fun c₄ ⟨kc, mc⟩ => k c₄ ⟨?_, ⟨M₀, ?_⟩, ?_, ?_⟩
    · have h := frame_writeBytes c₃.mem (emA s + BitVec.ofNat 64 (3 + (stackArg s 1).toNat))
        (Spec.Rsa.bytesAt c₃.mem (s.gpr .r9) (s.gpr .r10).toNat)
      rw [bytesAt_length, add_ofNat_ofNat] at h
      have h' : Frame [⟨fb s + BitVec.ofNat 64 (oEM + (3 + (stackArg s 1).toNat)), (s.gpr .r10).toNat⟩]
          c₃.mem c₄.mem := by rw [mc, add_ofNat_ofNat]; exact h
      exact midc.frameW1 kc hp.ksc (by unfold oLr oEM oEM1; omega_arith) (by unfold oEM oEM1 frameBytes; omega_arith) h'
    · rw [mc, hM, P₃.mem, mem₅, ← hl3, writeBytes_append _ _ _ _ (by simp [bytesAt_length]; omega_arith)]
      rfl
    · rw [kc.get .r5, P₃.get .r5, r5₅]
    · rw [kc.get .r12, P₃.get .r12, r12₅]

theorem bytes_written {m : Mem} {q : Addr} {xs : List Byte} {n : Nat} (hl : xs.length = n) (hn : n < 2 ^ 64) :
    Spec.Rsa.bytesAt (writeBytes m q xs) q n = xs := by
  subst hl; exact Proof.RsaPkcs1Sig.bytesAt_writeBytes _ _ _ hn

/-- At the call: `EM` complete, the zero test in its word, and the call's
arguments. -/
structure AtCall (s t : State) : Prop extends EMid s t where
  emb : Spec.Rsa.bytesAt t.mem (emA s) (s.gpr .r6).toNat = Spec.RsaPkcs1Enc.encode (msgB s) (psB s)
  slot : t.mem.readW (fb s + BitVec.ofNat 64 oZ) 64 = zbit (psB s)
  g3 : t.gpr .r3 = s.gpr .r3
  g4 : t.gpr .r4 = s.gpr .r6
  g5 : t.gpr .r5 = stackArg s 4
  g6 : t.gpr .r6 = stackArg s 5
  g7 : t.gpr .r7 = s.gpr .r7
  g8 : t.gpr .r8 = s.gpr .r8
  g9 : t.gpr .r9 = emA s
  g10 : t.gpr .r10 = s.gpr .r6
  a0 : stackArg t 0 = stackArg s 2
  a1 : stackArg t 1 = stackArg s 3

theorem encode_length {s : State} (hp : PreE s) :
    (Spec.RsaPkcs1Enc.encode (msgB s) (psB s)).length = (s.gpr .r6).toNat := by
  have := hp.ml; have := hp.pl
  simp [Spec.RsaPkcs1Enc.encode, bytesAt_length]; omega_arith

theorem callArgs_ok {s y : State} (hp : PreE s) (hy : EmDone s y) :
    WP isa (.block callArgs) y (AtCall s) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  obtain ⟨M₀, hM₀⟩ := hy.em
  have emb₀ : Spec.Rsa.bytesAt y.mem (emA s) (s.gpr .r6).toNat = Spec.RsaPkcs1Enc.encode (msgB s) (psB s) := by
    rw [hM₀, bytes_written (encode_length hp) (by omega_arith)]
  unfold callArgs
  have hz : InRegions y.wr (fb s + BitVec.ofNat 64 oZ) 8 := by rw [hy.wr]; exact in_fr s _ (by decide) (by decide)
  refine wp_std (a := fb s + BitVec.ofNat 64 oZ) (by rw [hy.g12]) hz fun y₁ m₁ => ?_
  refine wp_mov fun y₂ o₂ e₂ => wp_mov fun y₃ o₃ e₃ => wp_mov fun y₄ o₄ e₄ => wp_mov fun y₅ o₅ e₅ =>
    wp_addi fun y₆ o₆ e₆ => wp_mov fun y₇ o₇ e₇ => ?_
  have fr₁ : Frame [⟨fb s + BitVec.ofNat 64 oZ, 8⟩] y.mem y₁.mem := by
    rw [m₁.mem]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have mid₁ : EMid s y₁ := hy.toMid.frameW1 m₁.keep hp.ksc (by decide) (by decide) fr₁
  have O₇ : Only [.r3, .r4, .r7, .r8, .r9, .r10] y₁ y₇ :=
    (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇))))).mono
  have mid₇ : EMid s y₇ := mid₁.only O₇
  have r12₇ : y₇.gpr .r12 = fb s := by rw [O₇.get .r12, m₁.gpr, hy.g12]
  unfold callArgs at *
  refine wp_ld (a := stackArgAddr s 2) (by rw [r12₇, stackArgAddr_fb])
    (by rw [mid₇.rd]; exact arg_rd hp _ (by decide)) fun y₈ o₈ e₈ => ?_
  rw [arg_mid hp mid₇.mem (by decide)] at e₈
  refine wp_std (a := fb s + BitVec.ofNat 64 96) (by rw [o₈.get .r12, r12₇])
    (by rw [o₈.wr, mid₇.wr]; exact in_fr s _ (by decide) (by decide)) fun y₉ m₉ => ?_
  have fr₉ : Frame [⟨fb s + BitVec.ofNat 64 96, 16⟩] y₇.mem y₉.mem := by
    rw [m₉.mem, o₈.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains (fb s) (d := 96) (e := 96) (by decide) (by decide) (by decide))
  have K₉ : Frame [kR s, scR s] s.mem y₉.mem := mid₇.mem.trans (fr₉.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., Proof.RsaPkcs1Sig.PPC64LE.frame_sub s (d := 96) (n := 16) (by decide)⟩)
  refine wp_ld (a := stackArgAddr s 3) (by rw [m₉.gpr, o₈.get .r12, r12₇, stackArgAddr_fb])
    (by rw [m₉.rd, o₈.rd, mid₇.rd]; exact arg_rd hp _ (by decide)) fun y₁₀ o₁₀ e₁₀ => ?_
  rw [arg_mid hp K₉ (by decide)] at e₁₀
  refine wp_std (a := fb s + BitVec.ofNat 64 104) (by rw [o₁₀.get .r12, m₉.gpr, o₈.get .r12, r12₇])
    (by rw [o₁₀.wr, m₉.wr, o₈.wr, mid₇.wr]; exact in_fr s _ (by decide) (by decide)) fun y₁₁ m₁₁ => ?_
  have fr₁₁ : Frame [⟨fb s + BitVec.ofNat 64 96, 16⟩] y₇.mem y₁₁.mem := by
    rw [m₁₁.mem, o₁₀.mem]
    exact fr₉.writeW (List.mem_singleton_self _) _
      (Offset.contains (fb s) (d := 104) (e := 96) (by decide) (by decide) (by decide))
  have K₁₁ : Frame [kR s, scR s] s.mem y₁₁.mem := mid₇.mem.trans (fr₁₁.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., Proof.RsaPkcs1Sig.PPC64LE.frame_sub s (d := 96) (n := 16) (by decide)⟩)
  have r12₁₁ : y₁₁.gpr .r12 = fb s := by rw [m₁₁.gpr, o₁₀.get .r12, m₉.gpr, o₈.get .r12, r12₇]
  have rd₁₁ : y₁₁.rd = s.rd := by rw [m₁₁.rd, o₁₀.rd, m₉.rd, o₈.rd, mid₇.rd]
  refine wp_ld (a := stackArgAddr s 4) (by rw [r12₁₁, stackArgAddr_fb])
    (by rw [rd₁₁]; exact arg_rd hp _ (by decide)) fun y₁₂ o₁₂ e₁₂ => ?_
  refine wp_ld (a := stackArgAddr s 5) (by rw [o₁₂.get .r12, r12₁₁, stackArgAddr_fb])
    (by rw [o₁₂.rd, rd₁₁]; exact arg_rd hp _ (by decide)) fun y₁₃ o₁₃ e₁₃ => wp_nil ?_
  rw [arg_mid hp K₁₁ (by decide)] at e₁₂
  rw [o₁₂.mem, arg_mid hp K₁₁ (by decide)] at e₁₃
  have O₁₃ : Only [.r5, .r6] y₁₁ y₁₃ := o₁₂.trans o₁₃
  have g₁₁ : ∀ r, r ∉ [Reg.r0] → y₁₁.gpr r = y₇.gpr r := fun r hr => by
    rw [m₁₁.gpr, o₁₀.gpr r hr, m₉.gpr, o₈.gpr r hr]
  have hd96 : ∀ {d k : Nat}, 112 ≤ d → d + k ≤ frameBytes →
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, k⟩ ⟨fb s + BitVec.ofNat 64 96, 16⟩ := fun h₁ h₂ =>
    Offset.disjoint _ (.inr (by omega_arith)) (by unfold frameBytes at h₂; omega_arith) (by decide)
  have hEM : (⟨emA s, (s.gpr .r6).toNat⟩ : Region) = ⟨fb s + BitVec.ofNat 64 oEM, (s.gpr .r6).toNat⟩ := rfl
  have emb₁ : Spec.Rsa.bytesAt y₁.mem (emA s) (s.gpr .r6).toNat = Spec.RsaPkcs1Enc.encode (msgB s) (psB s) := by
    rw [Proof.RsaPkcs1Sig.bytes_apart (R := ⟨emA s, (s.gpr .r6).toNat⟩) fr₁
      (Offset.disjoint _ (.inr (by decide)) (by unfold oEM oEM1; omega_arith) (by decide)) (by dsimp only; omega_arith), emb₀]
  have hdS : ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 96, 16⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 oSave, 32⟩ r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd96 (by decide) (by decide)
  have hdL : ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 96, 16⟩ : Region)],
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 oLr, 64 / 8⟩ r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hd96 (by decide) (by decide)
  have hsv : Spill.Saved (fb s) s.gpr saved y₁₃.mem := by
    rw [O₁₃.mem]; exact mid₇.sv.frame_in saved_offs fr₁₁ hdS
  have hls : y₁₃.mem.readW (fb s + BitVec.ofNat 64 oLr) 64 = s.lr := by
    rw [O₁₃.mem, fr₁₁.readW (Region.contains_self _ _) hdL (by decide)]; exact mid₇.ls
  have hK : Frame [kR s, scR s] s.mem y₁₃.mem := by rw [O₁₃.mem]; exact K₁₁
  have hm := Mid.of mid₇ (w := y₁₃) (fun r hr => by rw [O₁₃.gpr r (by revert r; decide), g₁₁ r (by revert r; decide)])
    (by rw [O₁₃.sp, m₁₁.sp, o₁₀.sp, m₉.sp, o₈.sp]) (by rw [O₁₃.rd, rd₁₁, mid₇.rd])
    (by rw [O₁₃.wr, m₁₁.wr, o₁₀.wr, m₉.wr, o₈.wr]) hK hsv hls
  refine ⟨hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [O₁₃.mem, Proof.RsaPkcs1Sig.bytes_apart (R := ⟨emA s, (s.gpr .r6).toNat⟩) fr₁₁
      (hd96 (by decide) (by unfold oEM oEM1 frameBytes; omega_arith)) (by dsimp only; omega_arith), O₇.mem, emb₁]
  · have hdZ : ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 96, 16⟩ : Region)],
        Region.Disjoint ⟨fb s + BitVec.ofNat 64 oZ, 64 / 8⟩ r := fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd96 (by decide) (by decide)
    rw [O₁₃.mem, fr₁₁.readW (Region.contains_self _ _) hdZ (by decide), O₇.mem, m₁.mem,
      Mem.readW_writeW_self64, hy.g5]
  · rw [O₁₃.get .r3, g₁₁ .r3 (by decide), o₇.get .r3, o₆.get .r3, o₅.get .r3, o₄.get .r3, o₃.get .r3, e₂,
      mid₁.r28]
  · rw [O₁₃.get .r4, g₁₁ .r4 (by decide), o₇.get .r4, o₆.get .r4, o₅.get .r4, o₄.get .r4, e₃, o₂.get .r29,
      mid₁.r29]
  · rw [o₁₃.get .r5, e₁₂]
  · rw [e₁₃]
  · rw [O₁₃.get .r7, g₁₁ .r7 (by decide), o₇.get .r7, o₆.get .r7, o₅.get .r7, e₄, o₃.get .r30, o₂.get .r30,
      mid₁.r30]
  · rw [O₁₃.get .r8, g₁₁ .r8 (by decide), o₇.get .r8, o₆.get .r8, e₅, o₄.get .r31, o₃.get .r31, o₂.get .r31,
      mid₁.r31]
  · rw [O₁₃.get .r9, g₁₁ .r9 (by decide), o₇.get .r9, e₆, o₅.get .r12, o₄.get .r12, o₃.get .r12, o₂.get .r12,
      m₁.gpr, hy.g12]
  · rw [O₁₃.get .r10, g₁₁ .r10 (by decide), e₇, o₆.get .r29, o₅.get .r29, o₄.get .r29, o₃.get .r29,
      o₂.get .r29, mid₁.r29]
  · show y₁₃.mem.readW (stackArgAddr y₁₃ 0) 64 = _
    rw [stackArgAddr_in, O₁₃.sp, m₁₁.sp, o₁₀.sp, m₉.sp, o₈.sp, mid₇.sp, O₁₃.mem, m₁₁.mem, o₁₀.mem,
      Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide) (by decide)) (by decide), m₉.mem,
      Mem.readW_writeW_self64]
    exact e₈
  · show y₁₃.mem.readW (stackArgAddr y₁₃ 1) 64 = _
    rw [stackArgAddr_in, O₁₃.sp, m₁₁.sp, o₁₀.sp, m₉.sp, o₈.sp, mid₇.sp, O₁₃.mem, m₁₁.mem,
      Mem.readW_writeW_self64, e₁₀]

/-- `EM`, of `k` bytes. -/
abbrev emR (s : State) : Region := ⟨emA s, (s.gpr .r6).toNat⟩

theorem em_sub {s : State} (hp : PreE s) : Region.Sub (emR s) (kR s) :=
  Proof.RsaPkcs1Sig.PPC64LE.frame_sub s (d := oEM) (n := (s.gpr .r6).toNat) (by have := hp.k2; unfold oEM oEM1 frameBytes; omega_arith)

theorem oR_eq {s : State} (hp : PreE s) : oR s = ⟨s.gpr .r3, (s.gpr .r6).toNat⟩ := by
  rw [oR, hp.ok]

theorem pdOk_of {s t : State} (hp : PreE s) (ha : AtCall s t) : PdOk t := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hfb := fb_toNat hp.sp1
  have hsa : stackArgAddr t 0 = fb s + BitVec.ofNat 64 96 := by rw [stackArgAddr_in, ha.sp]
  have hko : (kR s).Disjoint ⟨s.gpr .r3, (s.gpr .r6).toNat⟩ := by rw [← oR_eq hp]; exact hp.ko
  refine ⟨?hl, ?sp, ?hrd, ?hwr, ?hk, ?h6, ?h10, ?he1, ?he2, ?hs⟩
  case hl =>
    rw [ha.g3, ha.g4, ha.g5, ha.g6, ha.g7, ha.g8, ha.g9, ha.g10, ha.a0, ha.a1, hsa]
    exact {
      on := by rw [← oR_eq hp]; exact hp.op
      oe := by rw [← oR_eq hp]; exact hp.oe
      oi := (hko.sub_left (em_sub hp)).symm
      os := by rw [← oR_eq hp]; exact hp.osc
      oa := (hko.sub_left (Proof.RsaPkcs1Sig.PPC64LE.frame_sub s (d := 96) (n := 16) (by decide))).symm
      ns := hp.sp.symm
      es := hp.es
      is := hp.ksc.sub_left (em_sub hp)
      sa := (hp.ksc.sub_left (Proof.RsaPkcs1Sig.PPC64LE.frame_sub s (d := 96) (n := 16) (by decide))).symm
      wo := by have := hp.wo; rw [hp.ok] at this; exact this
      wn := hp.wp
      we := hp.we
      wi := by
        show (fb s + BitVec.ofNat 64 oEM).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEM oEM1 frameBytes at *; omega_arith
      ws := hp.wsc }
  case sp => rw [ha.sp]; unfold frameBytes at hfb; omega_arith
  case hrd =>
    simp only [pdRd]
    rw [ha.g5, ha.g6, ha.g7, ha.g8, ha.g9, ha.g10, hsa, ha.rd, ha.wr]
    have hm : ∀ r ∈ s.rd, Covers [r] (s.rd ++ (fr s :: s.wr)) := fun r hr =>
      Covers.left (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact hr)
    refine Covers.cons (hm _ (by rw [hp.hrd]; simp)) (Covers.cons (hm _ (by rw [hp.hrd]; simp))
      (Covers.cons (Covers.one (in_fr' s _ _ (by decide) (by unfold oEM oEM1 frameBytes; omega_arith)))
        (Covers.one (in_fr' s _ _ (by decide) (by decide)) |>.cons Covers.nil)))
  case hwr =>
    simp only [pdWr]
    rw [ha.g3, ha.g4, ha.a0, ha.a1, ha.wr]
    exact Covers.of_mem fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact List.mem_cons_of_mem _ (by rw [hp.hwr, oR_eq hp]; simp)
      · exact List.mem_cons_of_mem _ (by rw [hp.hwr]; simp)
  case hk => rw [ha.g4]; exact ⟨hk1, hk2⟩
  case h6 => rw [ha.g6, ha.g4]; exact hp.hp
  case h10 => rw [ha.g10, ha.g4]
  case he1 => rw [ha.g8]; exact hp.e1
  case he2 => rw [ha.g8, ha.g4]; exact hp.e2
  case hs => rw [ha.g4, ha.a1]; exact hp.hs

/-- `pre` holds the values of the modulus. -/
def PreOk (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 4) (stackArg s 5).toNat)

/-- RSAEP of `EM`, as the entry state gives it. -/
def pubOut (s : State) : Option (List Byte) :=
  Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat) (Spec.RsaPkcs1Enc.encode (msgB s) (psB s))

/-- After the call: what the restores need, `out` and `k` kept, the zero
test in its word, and `out` written with RSAEP's result if `pre` holds the
modulus' values. -/
structure AfterCall (s t : State) : Prop where
  sv : Saves s t
  rd : t.rd = s.rd
  r28 : t.gpr .r28 = s.gpr .r3
  r29 : t.gpr .r29 = s.gpr .r6
  slot : t.mem.readW (fb s + BitVec.ofNat 64 oZ) 64 = zbit (psB s)
  res : PreOk s → Spec.Rsa.written t.mem (s.gpr .r3) (s.gpr .r6).toNat ((t.gpr .r3).setWidth 32) (pubOut s)

theorem call_ok {s t : State} (hp : PreE s) (ha : AtCall s t) : WP isa pubCall t (AfterCall s) := by
  have hk2 := hp.k2
  refine pdCall (pdOk_of hp ha) fun s' hrd' hwr' hsp' hf hpres hpost => ?_
  simp only [pdWr] at hf
  rw [ha.g3, ha.g4, ha.a0, ha.a1] at hf
  have hko : (kR s).Disjoint ⟨s.gpr .r3, (s.gpr .r6).toNat⟩ := by rw [← oR_eq hp]; exact hp.ko
  have hdF : ∀ {d k : Nat}, d + k ≤ frameBytes →
      ∀ r ∈ [(⟨s.gpr .r3, (s.gpr .r6).toNat⟩ : Region), scR s],
        Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, k⟩ r := fun h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hko.sub_left (Proof.RsaPkcs1Sig.PPC64LE.frame_sub s h)
    · exact hp.ksc.sub_left (Proof.RsaPkcs1Sig.PPC64LE.frame_sub s h)
  refine ⟨⟨hsp'.trans ha.sp, hwr'.trans ha.wr, fun r hr => (hpres r (by revert r; decide)).trans (ha.hi r hr),
    ha.sv.frame hf fun p hp' => hdF (by have := saved_offs p hp'; unfold oSave frameBytes at *; omega_arith),
    by rw [hf.readW (Region.contains_self _ _) (hdF (by decide)) (by decide)]; exact ha.ls⟩,
    hrd'.trans ha.rd, (hpres .r28 (by decide)).trans ha.r28, (hpres .r29 (by decide)).trans ha.r29,
    by rw [hf.readW (Region.contains_self _ _) (hdF (by decide)) (by decide)]; exact ha.slot, fun hc => ?_⟩
  have hw : Spec.Rsa.wordsAt t.mem (t.gpr .r5) (t.gpr .r6).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 4) (stackArg s 5).toNat := by
    rw [ha.g5, ha.g6]; exact words_of_frame ha.mem hp.kp hp.sp hp.wp
  have := hpost (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    (by rw [ha.g4, bytesAt_length]) (by rw [hw]; exact hc)
  rw [ha.g3, ha.g4, ha.g7, ha.g8, ha.g9, ha.emb,
    bytes_of_frame ha.mem hp.ke hp.es.symm (by have := hp.we; omega_arith)] at this
  exact this

end VG.Proof.RsaPkcs1Enc.PPC64LE.Enc
