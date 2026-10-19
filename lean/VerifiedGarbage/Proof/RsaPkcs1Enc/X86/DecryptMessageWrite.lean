module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecryptMessageByte
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PrfMessage

/-! # A prefix invariant for bytewise PRF message construction -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

structure MessageWritten (g : Geometry) (bs : Fin 9 → List Byte) (s0 : State)
    (xs : List Byte) (n : Nat) (s : State) : Prop where
  context : Context g bs s
  frame : Frame [g.scratch sMsg 16] s0.mem s.mem
  keep : Keeps [.eax, .ecx] s0 s
  bytes : ∀ j < n, s.mem ((g.scratch sMsg 16).base + BitVec.ofNat 64 j) = xs.getD j 0

theorem MessageWritten.start {g : Geometry} {bs : Fin 9 → List Byte} {s : State}
    (h : Context g bs s) (xs : List Byte) : MessageWritten g bs s xs 0 s :=
  ⟨h, Frame.refl _ _, Keeps.refl _ _, fun _ hj => by omega⟩

theorem MessageWritten.after_store {g : Geometry} {bs : Fin 9 → List Byte} {s0 s t : State}
    {xs : List Byte} {n : Nat} (h : MessageWritten g bs s0 xs n s) (hn : n < 16)
    (ht : Context g bs t) (K : Keeps [.eax, .ecx] s t)
    (M : t.mem = s.mem.writeW ((g.scratch sMsg 16).base + BitVec.ofNat 64 n) (xs.getD n 0))
    (F : Frame [g.scratch sMsg 16] s.mem t.mem) : MessageWritten g bs s0 xs (n + 1) t := by
  refine ⟨ht, h.frame.trans F, h.keep.trans K, ?_⟩
  intro j hj
  rw [M, WriteBytes.writeW8_apply]
  by_cases same : j = n
  · subst j; simp only [ite_true]
  · rw [ite_eq_right (Offset.add_ofNat_ne _ (by omega : j < 2 ^ 64) (by omega : n < 2 ^ 64) same)]
    exact h.bytes j (by omega)

theorem MessageWritten.put {g : Geometry} {bs : Fin 9 → List Byte} {s0 s : State}
    {xs : List Byte} {n v : Nat} (h : MessageWritten g bs s0 xs n s)
    (ptr : s0.gpr .edi = g.workspace + BitVec.ofNat 32 sMsg) (bound : n < 16)
    (byte : xs.getD n 0 = BitVec.ofNat 8 v) :
    WP isa (.block (putByte n v)) s (MessageWritten g bs s0 xs (n + 1)) := by
  refine WP.mono (messagePut_ok h.context ((h.keep.1 .edi (by decide)).trans ptr) bound v) ?_
  rintro t ⟨ht, M, F, K⟩
  exact h.after_store bound ht (K.mono (by decide)) (by rw [byte]; exact M) F

theorem MessageWritten.store {g : Geometry} {bs : Fin 9 → List Byte} {s0 s : State}
    {xs : List Byte} {n : Nat} (h : MessageWritten g bs s0 xs n s)
    (ptr : s0.gpr .edi = g.workspace + BitVec.ofNat 32 sMsg) (bound : n < 16)
    (r : Reg8) (byte : (s.gpr r.reg).setWidth 8 = xs.getD n 0) :
    WP isa (.block [.store8 ⟨.edi, n⟩ r]) s (MessageWritten g bs s0 xs (n + 1)) := by
  refine WP.mono (messageStore_ok h.context ((h.keep.1 .edi (by decide)).trans ptr) bound r) ?_
  rintro t ⟨ht, M, F, K⟩
  exact h.after_store bound ht (K.mono (by simp)) (by rw [byte] at M; exact M) F

theorem MessageWritten.update {g : Geometry} {bs : Fin 9 → List Byte} {s0 s t : State}
    {xs : List Byte} {n : Nat} (h : MessageWritten g bs s0 xs n s)
    (K : Keeps [.eax, .ecx] s t) (M : t.mem = s.mem) : MessageWritten g bs s0 xs n t :=
  ⟨h.context.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide)),
    by rw [M]; exact h.frame, h.keep.trans K, fun j hj => by rw [M]; exact h.bytes j hj⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec
