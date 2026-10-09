import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8AddChain
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8Digit

/-! Adding input blocks and their separately retained overflow. -/
namespace VG.Proof.Bignum.X86_64.AdxRotate8
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.AdxRotate8 (at_)

theorem xorRax_ok (s : State) :
    WP isa (.block [.alu32 .xor .rax (.reg .rax)]) s fun t =>
      t.gpr .rax = 0 ∧ t.cf = some false ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, Option.bind_some,
    State.setReg32, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg_self, BitVec.xor_self]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

theorem capture_ok (s : State) {c : Bool} (hc : s.cf = some c) (hz : s.gpr .rax = 0) :
    WP isa (.block [.adcx .rax (.reg .rax)]) s fun t =>
      t.cf = some false ∧ (t.gpr .rax).toNat = c.toNat ∧ Keeps [.rax] s t := by
  refine WP.mono (adcx_ok s (src := .reg .rax) rfl (fun _ h => nomatch h) hc)
    fun t ⟨ct, hct, _, et, kt⟩ => ?_
  rw [hz] at et
  simp only [show (0 : BitVec 64).toNat = 0 from rfl] at et
  have hb := Bool.toNat_le c
  have z : ct = false := Bool.toNat_eq_zero.mp (by omega_using [et, hb])
  subst z
  refine ⟨hct, ?_, kt⟩
  simpa using et

theorem addMem_ok {s : State} {B : Addr} {Z e : Nat} (hs : Scr s B Z)
    (hp : s.gpr .rsi = off B e) (he : e + 64 ≤ Z) :
    WP isa (.block AdxRotate8.addMem) s fun t =>
      cols t + 2 ^ 512 * (t.gpr .rax).toNat = cols s + wv s.mem B e 8 ∧
      (t.gpr .rax).toNat ≤ 1 ∧ t.cf = some false ∧
      Keeps [.rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  unfold AdxRotate8.addMem
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (xorRax_ok s) fun a ⟨za, hca, ka⟩ => ?_
  rw [WP.block_append_iff]
  have src : ∀ k < 8, ∀ t, Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] a t →
      readSrc t (.mem (at_ .rsi (8 * k))) = some (word s.mem B (e + 8 * k)) := by
    intro k hk t kt
    rw [kt.readMem (by simp [at_]) (by intro r h; nomatch h), ka.readMem (by simp [at_]) (by intro r h; nomatch h)]
    exact readSrc_word hs (ea_at hp (8 * k)) (by omega)
  refine WP.mono (chain_ok a _ _ hca src (fun _ _ _ h => nomatch h))
    fun b ⟨cb, hcb, eb, kb⟩ => ?_
  refine WP.mono (capture_ok b hcb ((kb.gpr (by decide)).trans za)) fun t ⟨hct, et, kt⟩ => ?_
  have ca := cols_keep ka.keep (by decide)
  have ct := cols_keep kt.keep (by decide)
  rw [number_words, ca] at eb
  refine ⟨?_, ?_, hct, (ka.trans (kb.trans kt)).mono (by decide)⟩
  · rw [ct, et]; simpa only [Bool.toNat_false, Nat.add_zero] using eb
  · rw [et]; exact Bool.toNat_le _

theorem capturePlus_ok (s : State) {c : Bool} (hc : s.cf = some c)
    (hz : s.gpr .rdx = 0) (hb : (s.gpr .rax).toNat < 2 ^ 64 - 1) :
    WP isa (.block [.adcx .rax (.reg .rdx)]) s fun t =>
      t.cf = some false ∧ (t.gpr .rax).toNat = (s.gpr .rax).toNat + c.toNat ∧ Keeps [.rax] s t := by
  refine WP.mono (adcx_ok s (src := .reg .rdx) rfl (fun _ h => nomatch h) hc)
    fun t ⟨ct, hct, _, et, kt⟩ => ?_
  rw [hz] at et
  simp only [show (0 : BitVec 64).toNat = 0 from rfl] at et
  have bc := Bool.toNat_le c
  have z : ct = false := Bool.toNat_eq_zero.mp (by omega_using [et, hb, bc])
  subst z
  refine ⟨hct, ?_, kt⟩
  simpa using et
theorem addWord_ok (s : State) (d : Int) {v : BitVec 64}
    (hm : readSrc s (.mem { base := .rcx, disp := d }) = some v)
    (hc : s.cf = some false) (hb : (s.gpr .rax).toNat < 2 ^ 64 - 1) :
    WP isa (.block (AdxRotate8.addWord { base := .rcx, disp := d })) s fun t =>
      cols t + 2 ^ 512 * (t.gpr .rax).toNat =
        cols s + 2 ^ 512 * (s.gpr .rax).toNat + v.toNat ∧
      (t.gpr .rax).toNat ≤ (s.gpr .rax).toNat + 1 ∧ t.cf = some false ∧
      Keeps [.rdx, .rax, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s t := by
  unfold AdxRotate8.addWord
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (movZero_ok s .rdx) fun a ⟨za, hca, _, ka⟩ => ?_
  rw [WP.block_append_iff]
  have src : ∀ k < 8, ∀ t, Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] a t →
      readSrc t (if k = 0 then .mem { base := .rcx, disp := d } else .reg .rdx) =
        some (if k = 0 then v else 0) := by
    intro k _ t kt
    by_cases hk : k = 0
    · simp only [hk, ↓reduceIte]
      rw [kt.readMem (by simp) (by intro r h; nomatch h), ka.readMem (by simp) (by intro r h; nomatch h)]
      exact hm
    · simp only [hk, ↓reduceIte, readSrc, kt.gpr (r := .rdx) (by decide), za]
  have imm : ∀ k < 8, ∀ n, (if k = 0 then Src.mem { base := .rcx, disp := d } else .reg .rdx) ≠ .imm n := by
    intro k _ n
    by_cases hk : k = 0 <;> simp [hk]
  refine WP.mono (chain_ok a _ _ (hca.trans hc) src imm) fun b ⟨cb, hcb, eb, kb⟩ => ?_
  have kbax : b.gpr .rax = s.gpr .rax := (kb.gpr (by decide)).trans (ka.gpr (by decide))
  refine WP.mono (capturePlus_ok b hcb ((kb.gpr (by decide)).trans za) (by rw [kbax]; exact hb))
    fun t ⟨hct, et, kt⟩ => ?_
  have ca := cols_keep ka.keep (by decide)
  have ct := cols_keep kt.keep (by decide)
  simp only [number, Nat.reduceEqDiff, ↓reduceIte, Bool.toNat_false,
    show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero] at eb
  rw [ca] at eb
  rw [kbax] at et
  refine ⟨?_, ?_, hct, (ka.trans (kb.trans kt)).mono (by decide)⟩
  · rw [ct, et]
    omega_using [eb]
  · rw [et]; have h := Bool.toNat_le cb; omega
end VG.Proof.Bignum.X86_64.AdxRotate8
