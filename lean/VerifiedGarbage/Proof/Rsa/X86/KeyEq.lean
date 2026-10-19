module

public import VerifiedGarbage.Proof.Rsa.X86.KeyScalar
public import VerifiedGarbage.Proof.Rsa.InverseArithmetic

/-! # Equality of native key arrays without data-dependent branches -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Proof.Rsa.KeyBits32
open VG.Proof.Rsa (borrow_iff)

theorem eqS_ok {s : State} {B : Addr} {Z w N d a b t : Nat} (h : Ws s B Z w N)
    (ht : t < N) (ha : a < N) (hb : b < N) (hta : t ≠ a) (htb : t ≠ b)
    (hd : d + 4 ≤ hdr) :
    WP isa (eqS w d a b t) s fun u => Ws u B Z w N ∧ Keep B w [t] [sT, d] s.mem u.mem ∧
      slot u.mem B d = (if num s.mem B w a = num s.mem B w b then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s u := by
  have hT : sT + 4 ≤ hdr := by decide
  rw [eqS, WP.seq_iff]
  refine WP.mono (sub3_ok h ht ha hb hta htb) fun u1 ⟨h1, k1, v1, b1, r1⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (store_slot h1 hT .ebx) fun u2 ⟨h2, k2, s2, r2⟩ => ?_
  rw [WP.seq_iff]
  refine WP.mono (sub3_ok h2 ht hb ha htb hta) fun u3 ⟨h3, k3, v3, b3, r3⟩ => ?_
  refine wp_orS (readSrc_sc h3.workspace (by have := h3.hdr_le; unfold sT hdr at *; omega)) fun s5 u5 => ?_
  refine wp_logicS (.inr rfl) rfl fun s6 u6 => ?_
  have h6 := (h3.rest u5.keeps (by decide) (by decide)).rest u6.keeps (by decide) (by decide)
  refine WP.mono (store_slot h6 hd .ebx) fun u ⟨h7, k7, e7, r7⟩ => ?_
  have mem : s6.mem = u3.mem := u6.mem.trans u5.mem
  rw [mem] at k7
  have fa := h.fit64 ha
  have fb := h.fit64 hb
  have na2 : num u2.mem B w a = num s.mem B w a := by
    rw [k2.num (by simp) (by simp; decide) fa, k1.num (by simpa using hta) (by simp) fa]
  have nb2 : num u2.mem B w b = num s.mem B w b := by
    rw [k2.num (by simp) (by simp; decide) fb, k1.num (by simpa using htb) (by simp) fb]
  rw [na2, nb2] at v3
  have sT3 : slot u3.mem B sT = (u1.gpr .ebx).toNat := by rw [k3.slot hT (by simp), s2]
  refine ⟨h7, (k1.join k2 (js := [t]) (ds := [sT, d])).join
    (k3.join k7 (js := [t]) (ds := [sT, d])) (js := [t]) (ds := [sT, d]), ?_, ?_⟩
  · rw [e7, u6.gpr, ite_eq_right (by decide), u5.gpr]
    have e : (u3.mem.readW (off B sT) 32).toNat = (u1.gpr .ebx).toNat := sT3
    rw [bv_nor_bits b3 (by rw [e]; exact b1), e]
    have p1 := borrow_iff v1 (val32_lt _ _ _ _) b1
    have p3 := borrow_iff v3 (val32_lt _ _ _ _) b3
    by_cases eq : num s.mem B w a = num s.mem B w b
    · have c1 := p1.mpr (by omega)
      have c3 := p3.mpr (by omega)
      simp [c1, c3, eq]
    · have c : ¬((u3.gpr .ebx).toNat = 0 ∧ (u1.gpr .ebx).toNat = 0) :=
        fun hh => eq (by have := p1.mp hh.2; have := p3.mp hh.1; omega)
      simp only [c, eq, ↓reduceIte]
  · exact r1.trans ((r2.mono (by decide)).trans (r3.trans ((u5.keeps.mono (by decide)).trans
      ((u6.keeps.mono (by decide)).trans (r7.mono (by decide))))))
end VG.Proof.Rsa.X86.Keys
