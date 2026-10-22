module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecCalls
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecMem
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecTaint

/-!
# RSAES-PKCS1-v1_5 decryption on x86: `DH = SHA256(D)`

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecHash.lean`): SHA-256's `init`,
`update` with `D` and `finalize` to `scratch + sDH`, each after the block of
its arguments (`hashD_vp`): `DH`, the SHA-256 digest of `D` (`H6`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp
open VG.Proof.Sha256.X86.Variants (Backend)

variable {P : EP}

/-! ## The blocks of arguments -/

/-- `d ← scratch + o`. -/
theorem St.scrW {σ s : State} (hs : S P σ s) {d : Reg} (hd : d ≠ .esp) (o : Nat) {is : List Instr}
    {Q : State → Prop} (k : ∀ t, S P σ t → Upd s t d (P.scr + BitVec.ofNat 32 o) → WP isa (.block is) t Q) :
    WP isa (.block (scr d o ++ is)) s Q := by
  simp only [scr, List.cons_append, List.nil_append]
  refine hs.2.wp_arg (j := 21) (r := d) (by simp) hd fun t1 s1 u1 => ?_
  refine wp_addi fun t2 u2 => k t2 ⟨hs.1, s1.upd u2 hd⟩ ⟨?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u2.gpr, u1.gpr]; rfl
  · rw [u2.other r hr, u1.other r hr]
  · rw [u2.mem, u1.mem]
  · rw [u2.rd, u1.rd]
  · rw [u2.wr, u1.wr]
  · rw [u2.syms, u1.syms]

/-- `d ← v`. -/
theorem St.movi {σ s : State} (hs : S P σ s) {d : Reg} (hd : d ≠ .esp) (v : Nat) {is : List Instr}
    {Q : State → Prop} (k : ∀ t, S P σ t → Upd s t d (BitVec.ofNat 32 v) → WP isa (.block is) t Q) :
    WP isa (.block (movI d v :: is)) s Q :=
  VG.X86.Wp.wp_movi fun t u => k t ⟨hs.1, hs.2.upd u hd⟩ u

/-- `d ← argument j`. -/
theorem St.argv {σ s : State} (hs : S P σ s) {j : Nat} (hj : j < 23) {d : Reg} (hd : d ≠ .esp)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t, S P σ t → Upd s t d (P.argv.getD j 0) → WP isa (.block is) t Q) :
    WP isa (.block (.mov d (arg j) :: is)) s Q :=
  hs.2.wp_arg (j := j) (r := d) (by simpa using hj) hd fun t st u => k t ⟨hs.1, st⟩ u

/-- The private-key operation's result, through changes of registers. -/
theorem Base.regs {σ s t : State} (h : Base P σ s) (st : P.lay.St σ t) (hm : t.mem = s.mem) : Base P σ t := by
  obtain ⟨hs, rc, pr, sl⟩ := h
  exact ⟨⟨hs.1, st⟩, rc, by rw [Priv, hm]; exact pr, by rw [hm]; exact sl⟩

/-! ## The stages -/

/-- Before `init`. -/
def H1 (P : EP) (σ s : State) : Prop := D4 P σ s ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 sSt

/-- After `init`. -/
def H2 (P : EP) (σ s : State) : Prop := D4 P σ s ∧ Spec.Sha256.Repr s.mem (sr P sSt 96).base []

/-- Before `update`. -/
def H3 (P : EP) (σ s : State) : Prop :=
  H2 P σ s ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 sSt ∧ s.gpr .esi = 0 ∧ s.gpr .eax = 0 ∧
    s.gpr .edx = P.scr + BitVec.ofNat 32 sD ∧ s.gpr .ecx = BitVec.ofNat 32 P.K ∧
    s.gpr .ebp = P.scr + BitVec.ofNat 32 sW

/-- After `update`. -/
def H4 (P : EP) (σ s : State) : Prop := Base P σ s ∧ Spec.Sha256.Repr s.mem (sr P sSt 96).base (Dfull P σ)

/-- Before `finalize`. -/
def H5 (P : EP) (σ s : State) : Prop :=
  H4 P σ s ∧ s.gpr .edi = P.scr + BitVec.ofNat 32 sSt ∧ s.gpr .eax = BitVec.ofNat 32 P.K ∧ s.gpr .ecx = 0 ∧
    s.gpr .edx = P.scr + BitVec.ofNat 32 sDH ∧ s.gpr .ebp = P.scr + BitVec.ofNat 32 sW

/-- `DH`. -/
def H6 (P : EP) (σ s : State) : Prop :=
  Base P σ s ∧ Spec.Rsa.bytesAt s.mem (sr P sDH 32).base 32 = Spec.Sha256.hash (Dfull P σ)

theorem D4.bytes_sr {σ s : State} (h : D4 P σ s) :
    Spec.Rsa.bytesAt s.mem (sr P sD P.K).base P.K = Dfull P σ := by
  rw [h.1.1.1.sr_eq (by decide)]; exact h.2

theorem shaInitArgs_vp : VP (D4 P) (.block shaInitArgs) (H1 P) :=
  VP.taint [.esp] shaInitArgs_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.2.sp, h₂.1.1.2.sp])
    fun σ s h => by
      rw [shaInitArgs, ← List.append_nil (scr _ _)]
      exact St.scrW h.1.1 (by decide) sSt fun t st u => WP.block_nil
        ⟨⟨h.1.regs st.2 u.mem, by rw [u.mem]; exact h.2⟩, u.gpr⟩

theorem shaInit_vp (v : Backend) : VP (H1 P) (callInit v.F) (H2 P) :=
  VP.shaInit v (sp := P.B) (fun σ s h => ⟨initA h.1.1.1 v h.2, h.1.1.1.2.sp⟩) fun σ s h s' a hr => by
    have hs := h.1.1.1
    have hK := hs.1.k1024
    have hws : ∀ r ∈ [sr P sSt 96], ∃ o n, o < 8448 ∧ o + n ≤ 8448 ∧ r = sr P o n := fun r hr => by
      simp only [List.mem_singleton] at hr; exact ⟨sSt, 96, by decide, by decide, hr⟩
    refine ⟨⟨h.1.1.call (k := 48) (by decide) hws a.rd a.wr a.esp a.frame, ?_⟩, hr⟩
    rw [← h.1.bytes_sr, ← hs.1.sr_eq (by decide)]
    refine keep_sr hs (by decide) a.frame (by decide) (by simp only [sD]; omega) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact hs.1.sr_sep (by simp only [sD, sSt]; omega) (by decide) (by decide) (by simp only [sD]; omega)
      (by decide)

theorem shaUpdArgs_vp : VP (H2 P) (.block shaUpdArgs) (H3 P) :=
  VP.taint [.esp] shaUpdArgs_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.1.2.sp, h₂.1.1.1.2.sp])
    fun σ s h => by
      have hs := h.1.1.1
      simp only [shaUpdArgs, List.append_assoc, List.cons_append, List.nil_append]
      refine St.scrW hs (d := .edi) (by decide) sSt fun t1 s1 u1 => ?_
      refine St.movi s1 (d := .esi) (by decide) 0 fun t2 s2 u2 => ?_
      refine St.movi s2 (d := .eax) (by decide) 0 fun t3 s3 u3 => ?_
      refine St.scrW s3 (d := .edx) (by decide) sD fun t4 s4 u4 => ?_
      refine St.argv s4 (j := 4) (by decide) (d := .ecx) (by decide) fun t5 s5 u5 => ?_
      rw [← List.append_nil (scr _ _)]
      refine St.scrW s5 (d := .ebp) (by decide) sW fun t6 s6 u6 => WP.block_nil ?_
      have mm : t6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
      refine ⟨⟨⟨h.1.1.regs s6.2 mm, by rw [mm]; exact h.1.2⟩, by rw [mm]; exact h.2⟩, ?_⟩
      simp (disch := decide) only [u6.gpr, u6.other, u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr, u3.other,
        u2.gpr, u2.other, u1.gpr]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem shaUpd_vp (v : Backend) : VP (H3 P) (callUpd v.F) (H4 P) :=
  VP.shaUpd v (sp := P.B) (c := 0) (len := P.K) (d := P.scr + BitVec.ofNat 32 sD)
    (fun σ s h => by
      have hs := h.1.1.1.1
      have hK := hs.1.k1024
      obtain ⟨_, edi, esi, eax, edx, ecx, ebp⟩ := h
      exact ⟨updA hs v edi esi eax ecx edx ebp (by omega)
        (Covers.right (St.cov_sr hs (o := sD) (n := P.K) (by decide) (by simp only [sD]; omega)))
        (hs.1.sr_sep (by simp only [sD, sSt]; omega) (by decide) (by decide) (by simp only [sD]; omega)
          (by decide))
        (hs.1.sr_sep (by simp only [sD, sW]; omega) (by decide) (by decide) (by simp only [sD]; omega)
          (by decide))
        (hs.1.below_sr (by decide) (by decide) (by simp only [sD]; omega))
        (hs.1.sr_fit (by decide) (by simp only [sD]; omega)), hs.2.sp⟩)
    fun σ s h s' a hp => by
      have hs := h.1.1.1.1
      have hws : ∀ r ∈ [sr P sSt 96, sr P sW 160], ∃ o n, o < 8448 ∧ o + n ≤ 8448 ∧ r = sr P o n :=
        fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ⟨sSt, 96, by decide, by decide, rfl⟩
          · exact ⟨sW, 160, by decide, by decide, rfl⟩
      refine ⟨h.1.1.1.call (k := 48) (by decide) hws a.rd a.wr a.esp a.frame, ?_⟩
      have := hp [] h.1.2 rfl
      rwa [List.nil_append, show Spec.Sha256.bytesAt s.mem ((P.scr + BitVec.ofNat 32 sD).setWidth 64) P.K =
        Dfull P σ from h.1.1.bytes_sr] at this

theorem shaFinArgs_vp : VP (H4 P) (.block shaFinArgs) (H5 P) :=
  VP.taint [.esp] shaFinArgs_taint (fun _ _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.1.2.sp, h₂.1.1.2.sp])
    fun σ s h => by
      have hs := h.1.1
      simp only [shaFinArgs, List.append_assoc, List.cons_append, List.nil_append]
      refine St.scrW hs (d := .edi) (by decide) sSt fun t1 s1 u1 => ?_
      refine St.argv s1 (j := 4) (by decide) (d := .eax) (by decide) fun t2 s2 u2 => ?_
      refine St.movi s2 (d := .ecx) (by decide) 0 fun t3 s3 u3 => ?_
      refine St.scrW s3 (d := .edx) (by decide) sDH fun t4 s4 u4 => ?_
      rw [← List.append_nil (scr _ _)]
      refine St.scrW s4 (d := .ebp) (by decide) sW fun t5 s5 u5 => WP.block_nil ?_
      have mm : t5.mem = s.mem := by rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
      refine ⟨⟨h.1.regs s5.2 mm, by rw [mm]; exact h.2⟩, ?_⟩
      simp (disch := decide) only [u5.gpr, u5.other, u4.gpr, u4.other, u3.gpr, u3.other, u2.gpr, u2.other,
        u1.gpr]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl

theorem shaFin_vp (v : Backend) : VP (H5 P) (callFin v.F) (H6 P) :=
  VP.shaFin v (sp := P.B) (lo := BitVec.ofNat 32 P.K) (hi := 0)
    (fun σ s h => by
      have hs := h.1.1.1
      obtain ⟨_, edi, eax, ecx, edx, ebp⟩ := h
      exact ⟨finA hs v (t := sDH) (by decide) (by decide) edi eax ecx edx ebp, hs.2.sp⟩)
    fun σ s h s' a hp => by
      have hs := h.1.1.1
      have hK := hs.1.k1024
      have hws : ∀ r ∈ [sr P sSt 96, sr P sDH 32, sr P sW 160], ∃ o n, o < 8448 ∧ o + n ≤ 8448 ∧
          r = sr P o n := fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨sSt, 96, by decide, by decide, rfl⟩
        · exact ⟨sDH, 32, by decide, by decide, rfl⟩
        · exact ⟨sW, 160, by decide, by decide, rfl⟩
      refine ⟨h.1.1.call (k := 48) (by decide) hws a.rd a.wr a.esp a.frame, ?_⟩
      have hl : (Dfull P σ).length = P.K := by
        simp [Proof.RsaPkcs1Sig.bytesAt_len]; have := hs.1.dlK; omega
      exact hp _ h.1.2 (by omega)
        (by rw [hl]; exact Proof.Pbkdf2.Stream.X86.zero_append_ofNat (by omega))

theorem hashD_vp (v : Backend) : VP (D4 P) (hashD v.F) (H6 P) :=
  shaInitArgs_vp.seq ((shaInit_vp v).seq (shaUpdArgs_vp.seq ((shaUpd_vp v).seq
    (shaFinArgs_vp.seq (shaFin_vp v)))))

end VG.Proof.RsaPkcs1Enc.X86.Dec
