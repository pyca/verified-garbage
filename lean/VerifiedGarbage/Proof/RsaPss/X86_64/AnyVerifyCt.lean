module

public import VerifiedGarbage.Proof.RsaPss.X86_64.AnySaltBackCT
public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyVerifyFixed
public import VerifiedGarbage.Proof.RsaPss.X86_64.AnyVerifyCorrect
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyCt
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT

/-!
# RSASSA-PSS verification on x86-64: constant time, and `Verified`

The prologue, the checks on the modulus and the salt's length (their
branches are on public values: the modulus' first byte and length, the
expected salt length), what follows them (`main_ctA`), and the epilogue, in
two runs whose entry states agree on the public data (`verify_ct`). With
`verify_correct`, `verify` meets `Spec.RsaPss.verifyContract`
(`verify_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Any

open VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaPss.X86_64.AnyHash (emLenAny saltFitsAny sHsel verifyTail dispatch mgfXorAny)
open VG.Proof.Dispatch.X86_64 (FlagsOnly)
open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (pubChkContract)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {G : Spec.Mgf1.Hash} {H : Hash} {k g : Nat}

/-- After the frame's push. -/
def J0A (s t : State) : Prop := t = allocState frameBytes s

/-- The words the prologue stores. -/
def K1A : List Nat := [15, 17, 18, 19, 20, 21, 22, 37, 38, 47, 48]

variable (H) in
/-- After the prologue: the modulus' first byte, and ZF set if it is zero. -/
def J1A (s t : State) : Prop :=
  VSA H s t K1A [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (vwrRA s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (n0v s) ∧ t.zf = some (decide (n0v s = 0))

variable (H) in
/-- After `emLen`: CF set if it is too short. -/
def J4A (s t : State) : Prop :=
  VSA H s t (K1A ++ [25, 26]) [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (vwrRA s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (veml s) ∧ t.cf = some (decide (veml s < H.D + 2))

variable (H) in
/-- After the salt length's arguments. -/
def J5A (s t : State) : Prop :=
  VSA H s t K5A [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (vwrRA s) s.mem t.mem ∧ t.gpr .rdx = vrdxA s ∧
    H.D + 2 ≤ veml s

theorem pro_ctA : RelCT isa (Two (VAtA G k g J0A)) (.block (AnyHash.verifyPrologue ++ n0)) (Two (VAtA G k g (J1A H))) := by
  obtain ⟨_, hc⟩ := vFixedA.pro
  have ar : ∀ (s : State) {r : Reg}, r ≠ .rsp → (allocState frameBytes s).gpr r = s.gpr r := fun s r hr => by
    rw [allocState_gpr']; exact ifn hr _ _
  refine two_post (two_pub0 1 [.rdi, .rsi, .rdx, .rcx, .r8, .r9] fb State.wr
    (fun a => [(.rdi, a.gpr .rdi), (.rsi, a.gpr .rsi), (.rdx, a.gpr .rdx), (.rcx, a.gpr .rcx), (.r8, a.gpr .r8),
      (.r9, a.gpr .r9)])
    (fun a t ⟨s, S, ht⟩ => ⟨by rw [ht, allocState_gpr', ifp rfl, ← S.fb], by rw [ht, ← S.wr, ← S.fb]; rfl,
      fun p hp => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> rw [ht, ar s (by decide)] <;>
          exact S.gpr (by decide)⟩)
    (fun a t ⟨s, S, _⟩ => S.rest) (fun _ => rfl) hc) fun a t ⟨s, S, ht⟩ => ?_
  subst ht
  have hp := S.ps
  rw [WP.block_append_iff]
  refine WP.mono (verifyPro_okA hp) fun t1 ⟨k1, L1, R1, f1⟩ => ?_
  have hM1 : Frame (vwrRA s) s.mem t1.mem := f1.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_cons_self .., vframe_sub s⟩
  refine WP.mono (vn0_okA hp L1 R1 (by simp [vproWA, upd]) k1.2.1 hM1) fun t2 ⟨k2, hm2, hax2, hz2⟩ =>
    ⟨s, S, ⟨L1.congr (k2.gpr (by decide)) k2.2.2 (by rw [hm2]), k2.2.2.trans k1.2.2,
      ⟨_, _, hm2 ▸ R1, fun k hk => ?_, trivial⟩, fun _ hp => by cases hp⟩, k2.2.1.trans k1.2.1, hm2 ▸ hM1, hax2, hz2⟩
  simp only [K1A, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [vproWA, upd, vwA]

/-- A refusal. -/
theorem fail_ctA {Φ : State → State → Prop}
    (hΦ : ∀ a t, Φ a t → ∃ s ks X, VSibA G k g a s ∧ VSA H s t ks [] X) :
    RelCT isa (Two Φ) verifyFail (Two (VAtA G k g (JRA H))) := by
  obtain ⟨_, hc⟩ := vFixed.fail
  have hv : ∀ a t, Φ a t → ∃ s, VSibA G k g a s ∧ VSA H s t [] [] fun _ _ => True := fun a t h => by
    obtain ⟨s, ks, X, S, v⟩ := hΦ a t h
    exact ⟨s, S, v.sub (fun _ h => by cases h) [] (fun _ hp => by cases hp) fun _ _ _ => trivial⟩
  refine two_post (vtwoA (G := G) (H := H) [] [] (fun _ => []) (fun a t h => let ⟨s, S, v⟩ := hv a t h; ⟨s, _, S, v⟩)
    (fun _ => rfl) (by decide) hc) fun a t h => ?_
  obtain ⟨s, S, v⟩ := hv a t h
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t.mem) ?_ rfl) fun t' ⟨hm, k⟩ =>
    ⟨s, S, v.keep k hm (by decide) fun _ hp => by cases hp⟩
  xrun [verifyFail]

theorem emLen_ctA (hH : HashOK H) (hGl : G.len = H.D) :
    RelCT isa (Two fun a t => VAtA G k g (J1A H) a t ∧ isa.eval .e t = some false) (.seq (.block smear) emLenAny)
      (Two (VAtA G k g (J4A H))) := by
  obtain ⟨_, hc⟩ := vFixedA.emLen
  refine two_post (vtwoA (G := G) (H := H) [15, 17] [.rax] (fun a => [(.rax, BitVec.ofNat 64 (n0v a))])
    (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.n0v]; exact h.2.2.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨⟨s, S, h⟩, he⟩ => ?_
  obtain ⟨v, hrd, hM, hax, hz⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  have hDN := hH.hDN; have hN := hH.N_le
  have h0 : n0v s ≠ 0 := fun h0 => by
    have : isa.eval .e t = some true := by rw [show isa.eval .e t = t.zf from rfl, hz, h0]; rfl
    rw [this] at he; cases he
  refine WP.seq (WP.mono (smear_ok t (x := n0v s) (BitVec.isLt _) h0 hax) fun t3 ⟨k3, hm3, hdx3, hz3⟩ => ?_)
  have L3 : Lay t3 (fb s) (stackArg s 4) := v.L.congr (k3.gpr (by decide)) k3.2.2 (by rw [hm3])
  have R3 : Rep t3.mem (fb s) (stackArg s 4) V W := hm3 ▸ R
  refine WP.mono (WP.keepIn (by safe_by [emLenAny]) (by exact Nat.zero_le 8)
    (emLenAny_ok (D := H.D) (by omega) L3 R3 (x := n0v s) (k := (s.gpr .rsi).toNat)
      (by rw [hw 17 (by decide)]; show s.gpr .rsi = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by rw [hw 15 (by decide)]; show s.gpr .r9 = _; rw [← hGl, ← hp.hdl, BitVec.ofNat_toNat, BitVec.setWidth_eq])
      (by omega) (by omega) hdx3 hz3)) fun t4 ⟨⟨L4, k4, R4, hax4, hc4⟩, f4⟩ =>
    ⟨s, S, ⟨L4, k4.2.2.trans (k3.2.2.trans v.wr), ⟨V, _, R4, fun k hk => ?_, trivial⟩, fun _ hp => by cases hp⟩,
      k4.2.1.trans (k3.2.1.trans hrd), vframe_keepA hp (k3.2.2.trans v.wr) L3.rsp (hm3 ▸ hM) f4, hax4, hc4⟩
  rcases List.mem_append.mp hk with hk | hk
  · have : k ≠ 25 ∧ k ≠ 26 := by simp only [K1A, List.mem_cons, List.not_mem_nil, or_false] at hk; omega
    simp only [upd]; rw [ifn this.2, ifn this.1]; exact hw k hk
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> simp [upd, vwA, vlo]

/-- `anyArgs`' first block. -/
theorem any1_okA {s : State} (hp : VPreA G s) {u : State} {S : Addr} (L : Lay u (fb s) S) (hrd : u.rd = s.rd)
    (hf : Frame (vwrRA s) s.mem u.mem) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem (fb s) S V W) :
    WP isa (.block any1A) u fun v => Lay v (fb s) S ∧ Keep [.rax] u v ∧ Rep v.mem (fb s) S V (upd W 36 (stackArg s 3)) ∧
      v.zf = some (decide ((stackArg s 2).setWidth 32 = 0)) := by
  have G' := L.geo
  have R1 := R.wf G' (k := 36) (by decide) (stackArg s 3)
  rw [show off (fb s) (8 * 36) = off (fb s) sSlen from rfl] at R1
  have hF := vfb_toNatA hp
  have := hp.sp2
  have a1 := varg_read'A hp hf (j := 3) (by decide)
  have a2 : (u.mem.writeW (off (fb s) sSlen) (stackArg s 3)).readW (off (fb s) (frameBytes + 8 + 8 * 2)) 32 =
      (stackArg s 2).setWidth 32 := by
    rw [readW32_low, Mem.readW_writeW_sep (Offset.sep _ (.inr (by unfold sSlen frameBytes; omega))
      (by unfold frameBytes; omega) (by unfold sSlen; omega)) (by decide), varg_read'A hp hf (j := 2) (by decide)]
  refine WP.mono (WP.keep [.rax] (Q := fun v => v.mem = u.mem.writeW (off (fb s) sSlen) (stackArg s 3) ∧
      v.zf = some (decide ((stackArg s 2).setWidth 32 = 0))) ?_ rfl) fun v ⟨⟨hm, hz⟩, hk⟩ =>
    ⟨L.of_rep' R (hm ▸ R1) (by simp [upd]) (hk.gpr (by decide)) hk.2.2, hk, hm ▸ R1, hz⟩
  xrun [any1A, arg, ea_sp, L.rsp, varg_inA hp hrd (j := 3) (by decide), varg_inA hp hrd (j := 2) (by decide) 4, a1, a2,
    L.st (d := sSlen) (by decide)]
  rw [BitVec.and_self, zext32_beq_zero]

variable (H) in
/-- Between `anyArgs`' blocks. -/
def JZA (s t : State) : Prop := VSA H s t [] [] (fun _ _ => True) ∧ t.zf = some (decide ((stackArg s 2).setWidth 32 = 0))

theorem anyArgs_ctA :
    RelCT isa (Two fun a t => VAtA G k g (J4A H) a t ∧ isa.eval .b t = some false) AnyHash.anyArgs (Two (VAtA G k g (J5A H))) := by
  obtain ⟨_, h1⟩ := vFixedA.any1
  obtain ⟨_, hT⟩ := vFixed.anyT
  obtain ⟨_, hE⟩ := vFixed.anyE
  refine two_post ?_ fun a t ⟨⟨s, S, ⟨v, hrd, hM, _, hcf⟩⟩, hb⟩ => ?_
  · rw [anyArgs_eqA]
    refine RelCT.seq (two_post (Ψ := VAtA G k g (JZA H)) (vtwoA (G := G) (H := H) [] [] (fun _ => [])
      (fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, S, h.1.sub (fun _ h => by cases h) _ (fun _ hp => by cases hp) fun _ _ x => x⟩)
      (fun _ => rfl) (by decide) h1) fun a t ⟨⟨s, S, ⟨v, hrd, hM, _⟩⟩, _⟩ => ?_)
      (two_ite (fun a t₁ t₂ ⟨s₁, S₁, _, z₁⟩ ⟨s₂, S₂, _, z₂⟩ => by
          rw [show isa.eval .e t₁ = t₁.zf from rfl, show isa.eval .e t₂ = t₂.zf from rfl, z₁, z₂, S₁.arg2, S₂.arg2])
        (vtwoA (G := G) (H := H) [] [] (fun _ => []) (fun a t ⟨⟨s, S, v, _⟩, _⟩ => ⟨s, _, S, v⟩) (fun _ => rfl)
          (by decide) hT)
        (vtwoA (G := G) (H := H) [] [] (fun _ => []) (fun a t ⟨⟨s, S, v, _⟩, _⟩ => ⟨s, _, S, v⟩) (fun _ => rfl)
          (by decide) hE))
    obtain ⟨V, W, R, -, -⟩ := v.W
    exact WP.mono (any1_okA S.ps v.L hrd hM R) fun u ⟨L', k', R', hz⟩ =>
      ⟨s, S, ⟨L', k'.2.2.trans v.wr, ⟨V, upd W 36 (stackArg s 3), R', (fun k (h : k ∈ ([] : List Nat)) => nomatch h),
        trivial⟩, fun _ hp => by cases hp⟩, hz⟩
  have hp := S.ps
  have hok : H.D + 2 ≤ veml s := by
    rw [show isa.eval .b t = t.cf from rfl, hcf] at hb
    simp only [Option.some.injEq, decide_eq_false_iff_not] at hb; omega
  obtain ⟨V, W, R, hw, -⟩ := v.W
  refine WP.mono (WP.keepIn (by safe_by [AnyHash.anyArgs]) (by exact Nat.zero_le 8)
    (anyArgs_okA hp v.L hrd hM R)) fun u ⟨⟨L', k', R', hdx⟩, f⟩ =>
    ⟨s, S, ⟨L', k'.2.2.trans v.wr, ⟨V, _, R', fun k hk => ?_, trivial⟩, fun _ hp => by cases hp⟩, k'.2.1.trans hrd,
      vframe_keepA hp v.wr v.L.rsp hM f, hdx, hok⟩
  by_cases h35 : k = 35
  · subst h35; simp [upd, vwA]
  by_cases h36 : k = 36
  · subst h36; simp [upd, vwA]
  simp only [upd]; rw [ifn h35, ifn h36]
  exact hw k (by simp only [K5A, K1A, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hk ⊢; omega)

theorem salt_ctA (hH : HashOK H) (hGl : G.len = H.D) :
    RelCT isa (Two (VAtA G k g (J5A H))) (.block (([.mov .rax (.mem (sp sK)), .mov .r8 (.mem (sp sLo)),
      .alu .sub .rax (.reg .r8)] : List Instr) ++ saltFitsAny)) (Two (VAtA G k g (J7A H))) := by
  obtain ⟨_, hc⟩ := vFixedA.salt
  refine two_post (vtwoA (G := G) (H := H) [15, 17, 26] [.rdx] (fun a => [(.rdx, vrdxA a)])
    (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.vrdxA]; exact h.2.2.2.1) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hM, hdx, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  have hDN := hH.hDN; have hN := hH.N_le
  have := vlo_le s
  have L := v.L
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .r8] (Q := fun u => u.gpr .rax = BitVec.ofNat 64 (veml s) ∧ u.mem = t.mem) ?_ rfl)
    fun t6 ⟨⟨hax6, hm6⟩, k6⟩ => ?_
  · xrun [ea_sp, L.rsp, L.ld (d := sK) (by decide), L.ld (d := sLo) (by decide), R.rd (d := sK) 17 rfl (by decide),
      R.rd (d := sLo) 26 rfl (by decide), hw 17 (by decide), hw 26 (by decide)]
    show s.gpr .rsi - BitVec.ofNat 64 (vlo s) = BitVec.ofNat 64 ((s.gpr .rsi).toNat - vlo s)
    apply BitVec.eq_of_toNat_eq
    have := (s.gpr .rsi).isLt
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have L6 : Lay t6 (fb s) (stackArg s 4) := L.congr (k6.gpr (by decide)) k6.2.2 (by rw [hm6])
  refine WP.mono (saltFitsAny_ok (D := H.D) L6 (hm6 ▸ R)
    (by rw [hw 15 (by decide)]; show s.gpr .r9 = _; rw [← hGl, ← hp.hdl, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (a := veml s) (b := vrdxA s) hok (by unfold veml; omega) hax6
    (by rw [k6.gpr (by decide)]; exact hdx)) fun t7 ⟨k7, hm7, hax7, hc7⟩ => ?_
  have hm : t7.mem = t.mem := by rw [hm7, hm6]
  exact ⟨s, S, v.keep (k6.trans k7) hm (by decide) (fun _ hp => by cases hp), k7.2.1.trans (k6.2.1.trans hrd),
    hm ▸ hM, hax7, hc7, hok⟩

theorem jc6_flags {a t t' : State} (h : VAtA G k g (JC6A H) a t) (hf : FlagsOnly t t') : VAtA G k g (JC6A H) a t' := by
  obtain ⟨s, S, ⟨v, hrd, hok⟩, fd, pos, val, hpos, hdx, hsi, h11⟩ := h
  have kk : Keep [] t t' := ⟨fun r _ => hf.gpr r, hf.rd, hf.wr⟩
  exact ⟨s, S, ⟨v.keep kk hf.mem (by decide) (fun _ hp => by cases hp), hf.rd.trans hrd, hok⟩, fd, pos, val, hpos,
    (hf.gpr _).trans hdx, (hf.gpr _).trans hsi, (hf.gpr _).trans h11⟩

variable (hH : HashOK H) (K : Callees H) (lk : MgfLink H hH) (hc : PssChecks H.P H.D)

include hH K hc in
/-- The dispatch on the digest's hash function, after `DB`'s first nonzero
byte is found. -/
theorem tail_ctA {hs : List Hash} (hkh : k < hs.length) (hl : hs.length ≤ 2 ^ 31) (hkH : hs[k] = H) :
    RelCT isa (Two (VAtA lk.G k g (JC6A H))) (dispatch sHsel verifyTail hs) (Two (VAtA lk.G k g (JRA H))) := by
  obtain ⟨_, hsel⟩ := vFixedA.selH
  refine dispatch_relCT (Ψ := VAtA lk.G k g (JC6A H)) hkh hl
    (vtwoA (G := lk.G) (H := H) [47] [] (fun _ => [])
      (fun a t ⟨s, S, h⟩ => ⟨s, _, S, h.1.1.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ x => x⟩)
      (fun _ => rfl) (by decide) hsel) (fun a t h => ?_) ?_
  · obtain ⟨s, S, ⟨v, hrd, hok⟩, fd, pos, val, hpos, hdx, hsi, h11⟩ := h
    obtain ⟨V, W, R, hw, -⟩ := v.W
    have h47 : W 47 = BitVec.ofNat 64 k := (hw 47 (by decide)).trans (by
      simp only [vwA]; rw [← S.hsel_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    have L := v.L
    have hr : t.mem.readW (off (fb s) sHsel) 64 = BitVec.ofNat 64 k := by
      rw [R.rd (d := sHsel) 47 rfl (by decide), h47]
    refine WP.mono (WP.keep [.rax] (Q := fun u => u.gpr .rax = BitVec.ofNat 64 k ∧ u.mem = t.mem) ?_ rfl)
      fun u ⟨⟨hax, hm⟩, kk⟩ => ⟨⟨s, S, ⟨v.keep kk hm (by decide) (fun _ hp => by cases hp), kk.2.1.trans hrd, hok⟩,
        fd, pos, val, hpos, (kk.gpr (by decide)).trans hdx, (kk.gpr (by decide)).trans hsi,
        (kk.gpr (by decide)).trans h11⟩, hax⟩
    xrun [ea_sp, L.rsp, L.ld (d := sHsel) (by decide), hr]
  · rw [hkH]
    exact ((posCheck_ctA hH hc.verify).seq (saltBack_ctA hH K lk hc)).mono
      (fun _ _ ⟨a, ⟨_, h₁, f₁⟩, ⟨_, h₂, f₂⟩⟩ => ⟨a, jc6_flags h₁ f₁, jc6_flags h₂ f₂⟩) fun _ _ h => h

include hH K hc in
theorem main_ctA (impl : PublicImpl) {hs : List Hash} (hkh : k < hs.length) (hg : g < hs.length)
    (hl : hs.length ≤ 2 ^ 31) (hkH : hs[k] = H) (hG : HashOK hs[g]) (KG : Callees hs[g]) (lkG : MgfLink hs[g] hG)
    (hcg : PssChecks hs[g].P hs[g].D) :
    RelCT isa (Two fun a t => VAtA lk.G k g (J7A H) a t ∧ isa.eval .b t = some false)
      (AnyHash.verifyMain hs impl.name impl.code) (Two (VAtA lk.G k g (JRA H))) := by
  unfold AnyHash.verifyMain
  simp only [seqs]
  exact RelCT.assoc (dbPub_ctA.seq ((call_ctA impl).seq (acc0_ctA.seq ((mgfAny_ctA hH lk hg hl hG KG lkG hcg).seq
    (clearTop_ctA.seq (posScan_ctA.seq (tail_ctA hH K lk hc hkh hl hkH)))))))

theorem restore_ctA : RelCT isa (Two (VAtA G k g (JRA H))) (.block restoreRegs) fun _ _ => True := by
  obtain ⟨_, hc⟩ := vFixed.restore
  exact vtwoA (G := G) (H := H) [] [] (fun _ => []) (fun a t ⟨s, S, v⟩ => ⟨s, _, S, v⟩) (fun _ => rfl) (by decide) hc

include hH K hc in
theorem body_ctA (impl : PublicImpl) {hs : List Hash} (hkh : k < hs.length) (hg : g < hs.length)
    (hl : hs.length ≤ 2 ^ 31) (hkH : hs[k] = H) (hG : HashOK hs[g]) (KG : Callees hs[g]) (lkG : MgfLink hs[g] hG)
    (hcg : PssChecks hs[g].P hs[g].D) :
    RelCT isa (Two (VAtA lk.G k g J0A)) (AnyHash.verifyBody hs impl.name impl.code) fun _ _ => True := by
  unfold AnyHash.verifyBody
  simp only [seqs]
  refine pro_ctA.seq ((two_ite (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
      rw [show isa.eval .e t₁ = t₁.zf from rfl, show isa.eval .e t₂ = t₂.zf from rfl, h₁.2.2.2.2, h₂.2.2.2.2,
        S₁.n0v, S₂.n0v])
    (fail_ctA (Φ := fun a t => VAtA lk.G k g (J1A H) a t ∧ isa.eval .e t = some true)
      fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, _, S, h.1⟩) (RelCT.assoc ((emLen_ctA hH lk.len).seq
      (two_ite (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
          rw [show isa.eval .b t₁ = t₁.cf from rfl, show isa.eval .b t₂ = t₂.cf from rfl, h₁.2.2.2.2, h₂.2.2.2.2,
            S₁.veml, S₂.veml])
        (fail_ctA (Φ := fun a t => VAtA lk.G k g (J4A H) a t ∧ isa.eval .b t = some true)
          fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, _, S, h.1⟩)
        (anyArgs_ctA.seq ((salt_ctA hH lk.len).seq (two_ite (fun a t₁ t₂ ⟨s₁, S₁, h₁⟩ ⟨s₂, S₂, h₂⟩ => by
            rw [show isa.eval .b t₁ = t₁.cf from rfl, show isa.eval .b t₂ = t₂.cf from rfl, h₁.2.2.2.2.1,
              h₂.2.2.2.2.1, S₁.veml, S₂.veml, S₁.vrdxA, S₂.vrdxA])
          (fail_ctA (Φ := fun a t => VAtA lk.G k g (J7A H) a t ∧ isa.eval .b t = some true)
            fun a t ⟨⟨s, S, h⟩, _⟩ => ⟨s, _, _, S, h.1⟩)
          (main_ctA hH K lk hc impl hkh hg hl hkH hG KG lkG hcg)))))))).seq restore_ctA)

include hH K hc in
/-- `verify` is constant time for the `k`th and `g`th hash functions. -/
theorem code_ctA (impl : PublicImpl) {hs : List Hash} (hkh : k < hs.length) (hg : g < hs.length)
    (hl : hs.length ≤ 2 ^ 31) (hkH : hs[k] = H) (hG : HashOK hs[g]) (KG : Callees hs[g]) (lkG : MgfLink hs[g] hG)
    (hcg : PssChecks hs[g].P hs[g].D) (hGk : Spec.HashId.mgf1 k = some lk.G) :
    RelCT isa (fun s₁ s₂ => (verifyAnyK.pre s₁ ∧ verifyAnyK.pre s₂ ∧ verifyAnyK.pub s₁ s₂) ∧ vhsel s₁ = k ∧
      vmsel s₁ = g) (AnyHash.verify hs impl.name impl.code) fun _ _ => True := by
  apply valloc
  apply (body_ctA hH K lk hc impl hkh hg hl hkH hG KG lkG hcg).mono
  · rintro _ _ ⟨s₁, s₂, ⟨⟨h₁, h₂, hpub⟩, hk, hg'⟩, e₁, e₂⟩
    have hk₂ : vhsel s₂ = k := by rw [← hk]; simp only [vhsel, hpub.2.2.2.2.2.2.2.2.2.1]
    have p₁ := VPreA.of lk.G h₁ (by rw [hk]; exact hGk)
    have p₂ := VPreA.of lk.G h₂ (by rw [hk₂]; exact hGk)
    exact ⟨s₁, ⟨s₁, ⟨p₁, vpub_reflA s₁, p₁, hk, hg'⟩, e₁⟩, ⟨s₂, ⟨p₁, hpub, p₂, hk, hg'⟩, e₂⟩⟩
  · exact fun _ _ h => h

end VG.Proof.RsaPss.X86_64.Any
