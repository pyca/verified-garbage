module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyEncoding
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyCmpArgs
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyStatus

/-! # The encoded-digest check is masked by the saved checked-RSA status -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify

def clobbers : List Reg := [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp]

def paddingResult (g : Geometry) (bs : Fin 5 → List Byte) (s : State) : BitVec 32 :=
  match encodeId g.hash (bs 2) g.length with
  | none => 0
  | some em => BitVec.ofNat 32 (decide (Spec.Rsa.bytesAt s.mem (byteAddr g.em1) g.length = em)).toNat &&& savedStatus g s

theorem ret0_ok (s : State) : WP isa ret0 s fun t =>
    t.gpr .eax = 0 ∧ t.mem = s.mem ∧ Keeps [.eax] s t := by
  unfold ret0
  refine wp_movS rfl fun t T _ => WP.block_nil ⟨T.gpr, T.mem, T.keeps⟩

theorem tail_ok {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) (enc : Encoded g bs s) :
    WP isa tail s fun t => Context g bs t ∧ t.mem = s.mem ∧ Keeps clobbers s t ∧
      t.gpr .eax = paddingResult g bs s := by
  unfold tail test0
  refine WP.seq (wp_cmpS rfl fun c C Z => WP.block_nil ?_)
  have hc := h.after (by rw [C.mem]; exact Frame.refl _ _) (C.keeps []) (congrFun C.gpr .esp)
  cases encoded : encodeId g.hash (bs 2) g.length with
  | none =>
    have zero : s.gpr .eax = 0 := by simpa only [Encoded, encoded] using enc
    refine WP.ite true (by simp [eval, Z, zero]) (fun _ => ?_) (by simp)
    refine WP.mono (ret0_ok c) ?_
    rintro t ⟨ax, M, K⟩
    have mt := M.trans C.mem
    have kt := (C.keeps clobbers).trans (K.mono (by decide))
    refine ⟨h.after (by rw [mt]; exact Frame.refl _ _) kt (kt.1 .esp (by decide)), mt, kt, ?_⟩
    simpa only [paddingResult, encoded] using ax
  | some em =>
    obtain ⟨one, bytes⟩ : s.gpr .eax = 1 ∧ Spec.Rsa.bytesAt s.mem (byteAddr g.em2) g.length = em := by
      simpa only [Encoded, encoded] using enc
    refine WP.ite false (by simp [eval, Z, one]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (cmpArgs_ok hc) ?_)
    rintro a ⟨ha, Ma, Ka, src, dst, cnt⟩
    refine WP.seq (WP.mono (compare_ok ha src dst cnt) ?_)
    rintro b ⟨hb, Mb, Kb, equal⟩
    refine WP.mono (result_ok hb) ?_
    rintro t ⟨ht, Mt, Kt, value⟩
    have ms : a.mem = s.mem := Ma.trans C.mem
    have mt := Mt.trans (Mb.trans ms)
    refine ⟨ht, mt, (C.keeps clobbers).trans ((Ka.mono (by decide)).trans
      ((Kb.mono (by decide)).trans (Kt.mono (by decide)))), ?_⟩
    have decision : decide (b.gpr .ebp = 0) = decide (Spec.Rsa.bytesAt a.mem (byteAddr g.em1) g.length = Spec.Rsa.bytesAt a.mem (byteAddr g.em2) g.length) := by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      exact equal
    simp only [paddingResult, encoded]
    rw [value, decision, ms, bytes]
    unfold savedStatus
    rw [Mb, ms]

end VG.Proof.RsaPkcs1Sig.X86.Ver
