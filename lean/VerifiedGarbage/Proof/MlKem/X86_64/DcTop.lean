module

public import VerifiedGarbage.Proof.MlKem.X86_64.DcDec
import VerifiedGarbage.Proof.MlKem.X86_64.EncTop
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86_64.DcDec
meta import VerifiedGarbage.Proof.MlKem.X86_64.EncTop
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.MlKem.X86_64.Decaps
public import VerifiedGarbage.Proof.MlKem.X86_64.Lay
import VerifiedGarbage.Proof.MlKem.X86_64.FragS
import VerifiedGarbage.Proof.MlKem.X86_64.FragHash
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Impl.MlKem.X86_64.Decaps
meta import VerifiedGarbage.Proof.MlKem.X86_64.Lay
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragS
meta import VerifiedGarbage.Proof.MlKem.X86_64.FragHash
meta import VerifiedGarbage.Proof.Framework.CallLay
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.MlKem.X86_64.Bytes
meta import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.MlKem.X86_64.Enc16

/-! ### `MlKem.X86_64.Dc16Dec`, which the modules that import this one used -/

section

/-!
# ML-KEM on x86-64: decapsulation with 16-bit polynomials, K-PKE.Decrypt

`m' = K-PKE.Decrypt(dk_PKE, c)` to `M`, in one call of
`vg_mlkem*_kpke_decrypt` (`dec_ok`, `dec_tr`), and what the rest of
decapsulation with 16-bit polynomials needs of the layout (`Dc16Wf`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Decaps16

open Decaps

variable (K : Kem16)

/-- What `vg_mlkem*_kpke_decrypt` writes. -/
abbrev kdW : List (Ptr × Nat) := [(sc oM, 32), (sc K.oZ, kScr)]

/-- What decapsulation with 16-bit polynomials needs of the layout, evaluated for each parameter set. -/
structure Dc16Wf : Prop extends DcWfB K.L oCT16 where
  kd : kdChk (dcB K.L) (dcW K.L) K.L (sc oM) (.rbp, 0) (.r14, 0) (sc K.oZ) = true
  kdK : dcChk K.L (kdW K) = true
  enc : Enc16.EncChks K (dcB K.L) (dcW K.L) (dckChk K.L) (.rbp, 384 * K.L.k)
  tl : Enc16.tailChk K (dcB K.L) (dcW K.L) (dckChk K.L) (.rbp, 384 * K.L.k) (sc oCT16) = true

variable {K}

/-- `m'` to `M`. -/
theorem dec_ok (hK : KpkeOk K.L) (W : Dc16Wf K) {σ : State} (hp : (decapsK K.L).pre σ) {s : State} (h : DC K.L σ s)
    (h15 : s.gpr .r15 = 1) : WP isa (K.L.kpkeDecAt (sc oM) (.rbp, 0) (.r14, 0) (sc K.oZ)) s (DM K.L σ) := by
  have L₀ := h.lay W.toDcWfB hp
  refine WP.mono (kpkeDecAt_okL hK L₀ (by decide) (by decide) rbx_na W.kd) fun s' ⟨hP, hm⟩ =>
    ⟨h.step W.toDcWfB hp hP.b W.kdK, by rw [hP.cs .r15 (by decide)]; exact h15, ?_⟩
  rw [hP.pa rbx_cs, hm, h.c, KPke.decM, KPke.dkPke, ← h.dk]
  exact congrArg (kpkeDecrypt K.L.p · _)
    (bytesAt_take _ _ (show 384 * K.L.p.k ≤ 768 * K.L.p.k + 96 by omega_using [])).symm

theorem dec_tr (hK : KpkeOk K.L) (W : Dc16Wf K) :
    RelCT isa (R K.L fun σ s => DC K.L σ s ∧ s.gpr .r15 = 1)
      (K.L.kpkeDecAt (sc oM) (.rbp, 0) (.r14, 0) (sc K.oZ)) fun _ _ => True :=
  rel2_of (kpkeDecAt_trL hK (by decide) (by decide) rbx_na W.kd) fun _ _ _ _ p₁ p₂ pub h₁ h₂ =>
    dc_lrel W.toDcWfB p₁ p₂ pub h₁.1 h₂.1

end Decaps16

end VG.Proof.MlKem.X86_64

end

end

/-! ### `MlKem.X86_64.DcSel`, which only this module used -/

section

/-!
# ML-KEM on x86-64: decapsulation, the choice of the key

The comparison of the ciphertexts of `N` bytes (`cmp_ok`: the OR of the XORs
of their words, 0 exactly when they are equal), the mask (`mid_ok`), and the choice of each byte of the key
(`sel_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.Sha3 (bytesAt)

namespace Decaps

open VG.Impl.MlKem.X86_64.Decaps

theorem cmpBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 8)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 8) :
    WP isa cmpBody s fun s' =>
      (s'.mem = s.mem ∧ s'.gpr .rdx = s.gpr .rdx ||| (s.mem.readW (s.gpr .rsi) 64 ^^^ s.mem.readW (s.gpr .rdi) 64) ∧
        s'.gpr .rsi = s.gpr .rsi + 8 ∧ s'.gpr .rdi = s.gpr .rdi + 8 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .r8, .rdx, .rsi, .rdi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold cmpBody
  xrun [h0, h1]

theorem selBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 1) (h2 : InRegions s.wr (s.gpr .r8) 1) :
    WP isa selBody s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .r8) (BitVec.setWidth 8 (((BitVec.setWidth 64 (s.mem (s.gpr .rsi)) ^^^
          BitVec.setWidth 64 (s.mem (s.gpr .rdi))) &&& s.gpr .rax) ^^^ BitVec.setWidth 64 (s.mem (s.gpr .rdi)))) ∧
        s'.gpr .rax = s.gpr .rax ∧ s'.gpr .rsi = s.gpr .rsi + 1 ∧ s'.gpr .rdi = s.gpr .rdi + 1 ∧
        s'.gpr .r8 = s.gpr .r8 + 1 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.r9, .r10, .rsi, .rdi, .r8, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold selBody
  xrun [h0, h1, h2]

/-- The block between the loops: the mask, and the pointers of the choice. -/
abbrev midB : List Instr := [.alu .sub .rdx (.imm 1), .alu .sbb .rax (.reg .rax), .mov .rsi (.reg .rbx),
  .alu .add .rsi (.imm (BitVec.ofNat 32 oG)), .mov .rdi (.reg .rbx), .alu .add .rdi (.imm (BitVec.ofNat 32 oKB)),
  .mov .r8 (.reg .r12), .mov32 .rcx (.imm 32)]

theorem mask_eq (x : BitVec 64) :
    0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (x.toNat < BitVec.toNat (1 : BitVec 64)))) =
      if x = 0 then BitVec.allOnes 64 else 0 := by
  by_cases h : x = 0
  · subst h; decide
  · have : ¬ x.toNat < 1 := fun h' => h (BitVec.eq_of_toNat_eq (by simp; omega_using [h']))
    rw [ifn h, show BitVec.toNat (1 : BitVec 64) = 1 from rfl, decide_eq_false this]
    decide

theorem mid_ok (s : State) :
    WP isa (.block midB) s fun s' =>
      (s'.mem = s.mem ∧ s'.gpr .rax = (if s.gpr .rdx = 0 then BitVec.allOnes 64 else 0) ∧
        s'.gpr .rsi = pa s (sc oG) ∧ s'.gpr .rdi = pa s (sc oKB) ∧ s'.gpr .r8 = pa s (.r12, 0) ∧
        s'.gpr .rcx = BitVec.ofNat 64 32) ∧
      Keep [.rax, .rdx, .rsi, .rdi, .r8, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [sx_ofNat (show oG < 2 ^ 31 by decide), sx_ofNat (show oKB < 2 ^ 31 by decide)]
  exact ⟨mask_eq _, by rw [pa, add_ofNat_zero]⟩

/-! ## The loops -/

theorem sel_byte (x y : Byte) (e : Bool) :
    BitVec.setWidth 8 (((BitVec.setWidth 64 x ^^^ BitVec.setWidth 64 y) &&& (if e then BitVec.allOnes 64 else 0)) ^^^
      BitVec.setWidth 64 y) = if e then x else y := by
  cases e
  · ext i hi; simp
  · rw [ifp rfl, ifp rfl, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    exact b8b x

theorem or_xor_eq_zero (d x y : BitVec 64) : d ||| (x ^^^ y) = 0 ↔ d = 0 ∧ x = y := by
  have bit : ∀ i, (d ||| (x ^^^ y)).getLsbD i = (d.getLsbD i || (x.getLsbD i ^^ y.getLsbD i)) := fun i => by
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor]
  constructor
  · intro h
    have hb : ∀ i, d.getLsbD i = false ∧ x.getLsbD i = y.getLsbD i := fun i => by
      have := congrArg (BitVec.getLsbD · i) h
      simp only [bit] at this
      cases hd : d.getLsbD i <;> cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp_all
    exact ⟨BitVec.eq_of_getLsbD_eq fun i _ => by rw [(hb i).1]; simp,
      BitVec.eq_of_getLsbD_eq fun i _ => (hb i).2⟩
  · rintro ⟨rfl, rfl⟩
    apply BitVec.eq_of_getLsbD_eq; intro i _
    simp

/-- Two words of memory are equal exactly when their eight bytes are. -/
theorem readW64_eq_iff (m : Mem) (a b : Addr) : m.readW a 64 = m.readW b 64 ↔ bytesAt m a 8 = bytesAt m b 8 := by
  constructor
  · intro h
    simp only [bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    rw [← byte_readW m a (show 8 * (i + 1) ≤ 64 by omega_using [hi]), h, byte_readW m b (show 8 * (i + 1) ≤ 64 by omega_using [hi])]
  · intro h
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    have e : ∀ c : Addr, (m.readW c 64).getLsbD j = ((m.readW c 64).extractLsb' (8 * (j / 8)) 8).getLsbD (j % 8) := by
      intro c; simp only [BitVec.getLsbD_extractLsb', show j % 8 < 8 from Nat.mod_lt _ (by decide), decide_true,
        Bool.true_and]; congr 1; omega_using []
    have hb := congrArg (fun l => l.getD (j / 8) 0) h
    simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show j / 8 < 8 by omega_using [hj]),
      Option.map_some, Option.getD_some] at hb
    rw [e a, e b, byte_readW m a (show 8 * (j / 8 + 1) ≤ 64 by omega_using [hj]),
      byte_readW m b (show 8 * (j / 8 + 1) ≤ 64 by omega_using [hj]), hb]

theorem bytesAt_eq_succ8 (m : Mem) (a b : Addr) (k : Nat) :
    bytesAt m a (8 * k + 8) = bytesAt m b (8 * k + 8) ↔
      bytesAt m a (8 * k) = bytesAt m b (8 * k) ∧
        m.readW (a + BitVec.ofNat 64 (8 * k)) 64 = m.readW (b + BitVec.ofNat 64 (8 * k)) 64 := by
  rw [bytesAt_add, bytesAt_add, readW64_eq_iff]
  exact ⟨fun h => List.append_inj h (by rw [bytesAt_length, bytesAt_length]), fun ⟨h₁, h₂⟩ => by rw [h₁, h₂]⟩

theorem cmp_ok (s : State) {N : Nat} (hN : N < 2 ^ 32) (hN0 : 0 < N) (h8 : N % 8 = 0) {a b : Addr}
    (ha : InRegions (s.rd ++ s.wr) a N) (hb : InRegions (s.rd ++ s.wr) b N)
    (hsi : s.gpr .rsi = a) (hdi : s.gpr .rdi = b) (hdx : s.gpr .rdx = 0) (hcx : s.gpr .rcx = BitVec.ofNat 64 (N / 8)) :
    WP isa (.loop cmpBody .ne) s fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (s'.gpr .rdx = 0 ↔ bytesAt s.mem a N = bytesAt s.mem b N) ∧
      Keep [.rax, .r8, .rdx, .rsi, .rdi, .rcx] s s' := by
  have in8 : ∀ {p : Addr}, InRegions (s.rd ++ s.wr) p N → ∀ k < N / 8,
      InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (8 * k)) 8 := fun h k hk => by
    obtain ⟨r, hr, hc⟩ := h
    exact ⟨r, hr, CallLay.contains_trans hc (by omega_using [hk]) (by omega_using [hN])⟩
  refine wp_countdown (cnt := .rcx) (N := N / 8) (by omega_using [hN]) (by omega_using [hN0, h8]) (fun k s' =>
      s'.gpr .rsi = a + BitVec.ofNat 64 (8 * k) ∧ s'.gpr .rdi = b + BitVec.ofNat 64 (8 * k) ∧
      (s'.gpr .rdx = 0 ↔ bytesAt s.mem a (8 * k) = bytesAt s.mem b (8 * k)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Keep [.rax, .r8, .rdx, .rsi, .rdi, .rcx] s s')
    (fun k hk s' ⟨hsi', hdi', hdx', hm', hrd', hwr', kk⟩ _ => ?_)
    (fun _ ⟨_, _, h1, h2, h3, h4, h5⟩ => ⟨h2, h3, h4, by rwa [show 8 * (N / 8) = N by omega_using [h8]] at h1, h5⟩)
    ⟨by rw [hsi]; simp, by rw [hdi]; simp, by rw [hdx]; simp [bytesAt], rfl, rfl, rfl, Keep.refl _ _⟩ hcx
  refine WP.mono (cmpBody_ok s' (by rw [hrd', hwr', hsi']; exact in8 ha k hk)
    (by rw [hrd', hwr', hdi']; exact in8 hb k hk)) fun s'' ⟨⟨hm, hdx, hsi'', hdi'', hcx, hz⟩, k'⟩ =>
      ⟨⟨by rw [hsi'', hsi', show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, off_add]; rfl,
        by rw [hdi'', hdi', show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, off_add]; rfl, ?_, hm.trans hm',
        k'.2.1.trans hrd', k'.2.2.trans hwr', (kk.trans k').mono (by decide)⟩, hcx, hz⟩
  rw [hdx, or_xor_eq_zero, hdx', hsi', hdi', hm', show 8 * (k + 1) = 8 * k + 8 by omega_using [], bytesAt_eq_succ8]

theorem sel_ok (s : State) {g kb key : Addr} (e : Bool) (hg : InRegions (s.rd ++ s.wr) g 32)
    (hkb : InRegions (s.rd ++ s.wr) kb 32) (hkey : InRegions s.wr key 32)
    (dg : Region.Disjoint ⟨g, 32⟩ ⟨key, 32⟩) (dkb : Region.Disjoint ⟨kb, 32⟩ ⟨key, 32⟩)
    (hsi : s.gpr .rsi = g) (hdi : s.gpr .rdi = kb) (h8 : s.gpr .r8 = key)
    (hax : s.gpr .rax = if e then BitVec.allOnes 64 else 0) (hcx : s.gpr .rcx = BitVec.ofNat 64 32) :
    WP isa (.loop selBody .ne) s fun s' =>
      bytesAt s'.mem key 32 = (if e then bytesAt s.mem g 32 else bytesAt s.mem kb 32) ∧
      Frame [⟨key, 32⟩] s.mem s'.mem ∧ Keep [.r9, .r10, .rsi, .rdi, .r8, .rcx] s s' := by
  refine WP.mono (wp_countdown (cnt := .rcx) (N := 32) (by decide) (by decide) (fun k s' =>
      s'.gpr .rsi = g + BitVec.ofNat 64 k ∧ s'.gpr .rdi = kb + BitVec.ofNat 64 k ∧
      s'.gpr .r8 = key + BitVec.ofNat 64 k ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨key, 32⟩] s.mem s'.mem ∧
      (∀ j < k, s'.mem (key + BitVec.ofNat 64 j) =
        if e then s.mem (g + BitVec.ofNat 64 j) else s.mem (kb + BitVec.ofNat 64 j)) ∧
      Keep [.r9, .r10, .rsi, .rdi, .r8, .rcx] s s')
    (fun k hk s' ⟨hsi', hdi', h8', hrd', hwr', hf, hc, kk⟩ _ => ?_) (fun _ h => h)
    ⟨by rw [hsi]; simp, by rw [hdi]; simp, by rw [h8]; simp, rfl, rfl, Frame.refl _ _,
      fun j hj => absurd hj (Nat.not_lt_zero _), Keep.refl _ _⟩ hcx) fun s' ⟨_, _, _, _, _, hf, hc, kk⟩ => ⟨?_, hf, kk⟩
  · have hax' : s'.gpr .rax = if e then BitVec.allOnes 64 else 0 := by rw [kk.gpr (by decide)]; exact hax
    refine WP.mono (selBody_ok s' (by rw [hrd', hwr', hsi']; exact inRegions_byte hg hk (by omega_using []))
      (by rw [hrd', hwr', hdi']; exact inRegions_byte hkb hk (by omega_using []))
      (by rw [hwr', h8']; exact inRegions_byte hkey hk (by omega_using [])))
      fun s'' ⟨⟨hm, hax'', hsi'', hdi'', h8'', hcx, hz⟩, k'⟩ =>
        ⟨⟨by rw [hsi'', hsi', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, off_add],
          by rw [hdi'', hdi', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, off_add],
          by rw [h8'', h8', show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, off_add],
          k'.2.1.trans hrd', k'.2.2.trans hwr', ?_, fun j hj => ?_, (kk.trans k').mono (by decide)⟩, hcx, hz⟩
    · rw [hm, h8']
      exact hf.writeW (List.mem_singleton_self _) _ (contains_offset' (by omega_using [hk]) (by omega_using []))
    · have eg : s'.mem (g + BitVec.ofNat 64 k) = s.mem (g + BitVec.ofNat 64 k) :=
        hf.bytes (R := ⟨g, 32⟩) (by simpa using dg) (show 32 ≤ 2 ^ 64 by decide) hk
      have ekb : s'.mem (kb + BitVec.ofNat 64 k) = s.mem (kb + BitVec.ofNat 64 k) :=
        hf.bytes (R := ⟨kb, 32⟩) (by simpa using dkb) (show 32 ≤ 2 ^ 64 by decide) hk
      rw [hm, h8', writeW8_apply]
      by_cases ej : j = k
      · subst ej
        rw [ifp rfl, hsi', hdi', hax', sel_byte, eg, ekb]
      · rw [ifn (fun h => ej (by have := congrArg BitVec.toNat h; simp at this; omega_using [hk, hj, this])), hc j (by omega_using [hj, ej])]
  · cases e
    · simp only [bytesAt, Bool.false_eq_true, ite_false]
      exact List.map_congr_left fun i hi => by simpa using hc i (List.mem_range.mp hi)
    · simp only [bytesAt, ite_true]
      exact List.map_congr_left fun i hi => by simpa using hc i (List.mem_range.mp hi)

/-! ## The choice -/

abbrev setupB (o n : Nat) : List Instr := [.mov .rsi (.reg .r14), .mov .rdi (.reg .rbx),
  .alu .add .rdi (.imm (BitVec.ofNat 32 o)), .mov32 .rcx (.imm (BitVec.ofNat 32 (n / 8))), .mov32 .rdx (.imm 0)]

theorem setup_ok {o n : Nat} (ho : o < 2 ^ 31) (hn : n < 2 ^ 32) (s : State) :
    WP isa (.block (setupB o n)) s fun s' =>
      (s'.mem = s.mem ∧ s'.gpr .rsi = pa s (.r14, 0) ∧ s'.gpr .rdi = pa s (sc o) ∧
        s'.gpr .rcx = BitVec.ofNat 64 (n / 8) ∧ s'.gpr .rdx = 0) ∧
      Keep [.rsi, .rdi, .rcx, .rdx] s s' := by
  refine WP.keep _ ?_ (by rfl)
  xrun [sx_ofNat ho, sw_ofNat (show n / 8 < 2 ^ 32 by omega_using [hn])]
  rw [pa, add_ofNat_zero]

theorem select_ok {o n : Nat} (ho : o < 2 ^ 31) (hn : n < 2 ^ 32) (hn0 : 0 < n) (h8 : n % 8 = 0)
    {s : State}
    (hc : InRegions (s.rd ++ s.wr) (pa s (.r14, 0)) n)
    (hct : InRegions (s.rd ++ s.wr) (pa s (sc o)) n) (hg : InRegions (s.rd ++ s.wr) (pa s (sc oG)) 32)
    (hkb : InRegions (s.rd ++ s.wr) (pa s (sc oKB)) 32) (hkey : InRegions s.wr (pa s (.r12, 0)) 32)
    (dg : Region.Disjoint ⟨pa s (sc oG), 32⟩ ⟨pa s (.r12, 0), 32⟩)
    (dkb : Region.Disjoint ⟨pa s (sc oKB), 32⟩ ⟨pa s (.r12, 0), 32⟩) :
    WP isa (selectAt o n) s fun s' => PPost s s' [((.r12, 0), 32)] ∧
      bytesAt s'.mem (pa s (.r12, 0)) 32 =
        if bytesAt s.mem (pa s (.r14, 0)) n = bytesAt s.mem (pa s (sc o)) n then
          bytesAt s.mem (pa s (sc oG)) 32 else bytesAt s.mem (pa s (sc oKB)) 32 := by
  unfold selectAt
  refine WP.seq (WP.mono (setup_ok ho hn s) fun s₁ ⟨⟨hm₁, hsi₁, hdi₁, hcx₁, hdx₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (cmp_ok s₁ hn hn0 h8 (by rw [k₁.2.1, k₁.2.2]; exact hc) (by rw [k₁.2.1, k₁.2.2]; exact hct) hsi₁ hdi₁
    hdx₁ hcx₁) fun s₂ ⟨hm₂, hrd₂, hwr₂, hdx₂, k₂⟩ => ?_)
  refine WP.seq (WP.mono (mid_ok s₂) fun s₃ ⟨⟨hm₃, hax₃, hsi₃, hdi₃, h8₃, hcx₃⟩, k₃⟩ => ?_)
  have e12 : ∀ r ∈ [Reg.rbx, Reg.r12], s₂.gpr r = s.gpr r := fun r hr => by
    rw [k₂.gpr (by simp at hr; rcases hr with rfl | rfl <;> decide),
      k₁.gpr (by simp at hr; rcases hr with rfl | rfl <;> decide)]
  have pG : pa s₂ (sc oG) = pa s (sc oG) := by rw [pa, pa, e12 .rbx (by simp)]
  have pKB : pa s₂ (sc oKB) = pa s (sc oKB) := by rw [pa, pa, e12 .rbx (by simp)]
  have pK : pa s₂ (.r12, 0) = pa s (.r12, 0) := by rw [pa, pa, e12 .r12 (by simp)]
  rw [pG] at hsi₃; rw [pKB] at hdi₃; rw [pK] at h8₃
  have hmem : s₃.mem = s.mem := by rw [hm₃, hm₂, hm₁]
  have hrd : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [k₃.2.1, k₃.2.2, hrd₂, hwr₂, k₁.2.1, k₁.2.2]
  have hwr : s₃.wr = s.wr := by rw [k₃.2.2, hwr₂, k₁.2.2]
  have hax : s₃.gpr .rax = if decide (bytesAt s.mem (pa s (.r14, 0)) n = bytesAt s.mem (pa s (sc o)) n) then
      BitVec.allOnes 64 else 0 := by
    rw [hax₃]
    rw [hm₁] at hdx₂
    exact ite_congr (propext (hdx₂.trans decide_eq_true_iff.symm)) (fun _ => rfl) (fun _ => rfl)
  refine WP.mono (sel_ok s₃ _ (by rw [hrd]; exact hg) (by rw [hrd]; exact hkb) (by rw [hwr]; exact hkey) dg dkb hsi₃
    hdi₃ h8₃ hax hcx₃) fun s₄ ⟨hb, hf, k₄⟩ => ⟨?_, ?_⟩
  · refine post_of_keep ((((k₁.trans k₂).trans k₃).trans k₄).mono (rs' := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10])
      (by decide)) (by decide) ?_
    rw [← hmem]; exact hf
  · rw [hb, hmem]
    simp only [decide_eq_true_eq]

end Decaps

end VG.Proof.MlKem.X86_64

end

end

/-!
# ML-KEM on x86-64: decapsulation

After K-PKE.Decrypt (`DcDec.lean`): `G(m' ‖ h)` and `J(z ‖ c)` (`hashes_ok`),
K-PKE.Encrypt in the context `dcX` (which keeps `K'` and `K̄`), and the choice
of the key (`select_okD`). The function returns 1 with
`ML-KEM.Decaps_internal(dk, c)` in `key` if every `SampleNTT` succeeded within
280 iterations (`allOk`), and 0 otherwise (`kemDecaps_correct`); it leaks
only the pointers and `ρ` (`kemDecaps_ct`). Each parameter set's file moves
this to its shared contract.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Decaps

open VG.Impl.MlKem.X86_64.Decaps

variable {L : Kem}

/-- `m'`, `(K', r') = G(m' ‖ h)`, `K̄ = J(z ‖ c)` and the encryption key of `σ`. -/
abbrev dcM' (L : Kem) (σ : State) : List Byte := KPke.decM L.p (dcDk L σ) (dcC L σ)
abbrev dcG (L : Kem) (σ : State) : List Byte × List Byte := G (dcM' L σ ++ KPke.dkH L.p (dcDk L σ))
abbrev dcKb (L : Kem) (σ : State) : List Byte := J (KPke.dkZ L.p (dcDk L σ) ++ dcC L σ)
abbrev dcEk (L : Kem) (σ : State) : List Byte := KPke.dkEk L.p (dcDk L σ)

/-- What `K-PKE.Encrypt` keeps: `DC`, `K'` at `G` and `K̄` at `KB`. -/
structure DCK (L : Kem) (σ s : State) : Prop where
  dc : DC L σ s
  k : bytesAt s.mem (pa s (sc oG)) 32 = (dcG L σ).1
  kb : bytesAt s.mem (pa s (sc oKB)) 32 = dcKb L σ

theorem DCK.step {oc : Nat} (W : DcWfB L oc) {σ : State} (hp : (decapsK L).pre σ) {s s' : State} (h : DCK L σ s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hc : dckChk L ws = true) : DCK L σ s' := by
  simp only [dckChk, Bool.and_eq_true] at hc
  have L₀ := h.dc.lay W hp
  exact ⟨h.dc.step W hp hP hc.1.1, by rw [L₀.keepBytes hP hc.1.2]; exact h.k, by rw [L₀.keepBytes hP hc.2]; exact h.kb⟩

/-- The context of `K-PKE.Encrypt` in a run from `σ`. -/
def dcX {oc : Nat} (W : DcWfB L oc) (σ : State) : Ctx (dcR L) (dcW L) where
  Out s := (decapsK L).pre σ ∧ DCK L σ s
  chk := dckChk L
  bs := dcB_bases L
  lay h := h.2.dc.lay W h.1
  step h hP hc := ⟨h.1, h.2.step W h.1 hP hc⟩

/-- The context of `K-PKE.Encrypt` in any run. -/
def dcXA {oc : Nat} (W : DcWfB L oc) : Ctx (dcR L) (dcW L) where
  Out s := ∃ σ, (decapsK L).pre σ ∧ DCK L σ s
  chk := dckChk L
  bs := dcB_bases L
  lay := fun ⟨_, hp, h⟩ => h.dc.lay W hp
  step := fun ⟨σ, hp, h⟩ hP hc => ⟨σ, hp, h.step W hp hP hc⟩

/-! ## `G(m' ‖ h)` and `J(z ‖ c)` -/

theorem shakeSuffix31 : BitVec.ofNat 8 0x1f = Spec.Sha3.shakeSuffix := by decide

/-- The inputs of `K-PKE.Encrypt`, and `r15 = 1`. -/
abbrev EncI {oc : Nat} (W : DcWfB L oc) (σ s : State) : Prop :=
  Enc.EIn L (dcX W σ) (.rbp, 384 * L.k) (dcEk L σ) (dcM' L σ) (dcG L σ).2 s ∧ s.gpr .r15 = 1

theorem hashes_ok {oc : Nat} (W : DcWfB L oc) {σ : State} (hp : (decapsK L).pre σ) {s : State} (h : DM L σ s) :
    WP isa (hashes L) s (EncI W σ) := by
  have L₀ := h.dc.lay W hp
  have hdk : 768 * L.k + 96 = L.dkLen := rfl
  unfold hashes
  -- `G(m' ‖ h)`.
  refine WP.seq (WP.mono (hash_ok (dcB_bases L) (ps := [(sc oM, 32), ((.rbp, 768 * L.k + 32), 32)]) (rate := 72)
    (out := sc oG) (len := 64) W.h₁ (show 6 < 256 by decide) L₀) fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have k₁ := h.dc.step W hp hP₁.b W.h₁K
  have L₁ := k₁.lay W hp
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, h.m,
    slice_of h.dc.dk (show 768 * L.k + 32 + 32 ≤ L.dkLen by omega_using [hdk]), KeyGen.sha3Suffix6] at hb₁
  rw [← sha3_512_eq, ← hP₁.pa rbx_cs] at hb₁
  -- `J(z ‖ c)`.
  refine WP.mono (hash_ok (dcB_bases L) (ps := [((.rbp, 768 * L.k + 64), 32), ((.r14, 0), L.ctLen)]) (rate := 136)
    (out := sc oKB) (len := 32) W.h₂ (show 0x1f < 256 by decide) L₁) fun s₂ ⟨hP₂, hb₂⟩ => ?_
  have k₂ := k₁.step W hp hP₂.b W.h₂K
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, k₁.c,
    slice_of k₁.dk (show 768 * L.k + 64 + 32 ≤ L.dkLen by omega_using [hdk]), shakeSuffix31] at hb₂
  rw [← J_eq, ← hP₂.pa rbx_cs] at hb₂
  have hG : bytesAt s₂.mem (pa s₂ (sc oG)) 64 = Spec.Sha3.sha3_512 (dcM' L σ ++ KPke.dkH L.p (dcDk L σ)) := by
    rw [L₁.keepBytes hP₂.b W.h₂G]; exact hb₁
  have hK : bytesAt s₂.mem (pa s₂ (sc oG)) 32 = (dcG L σ).1 := by
    rw [← bytesAt_take _ _ (show 32 ≤ 64 by decide), hG]; rfl
  have hr : bytesAt s₂.mem (pa s₂ sigP) 32 = (dcG L σ).2 := by
    have e := bytesAt_drop s₂.mem (pa s₂ (sc oG)) (k := 32) (len := 64) (by decide)
    have e' : (bytesAt s₂.mem (pa s₂ (sc oG)) 64).drop 32 = bytesAt s₂.mem (pa s₂ sigP) 32 := by
      rw [e, pa, pa, off_add]
    rw [← e', hG]; rfl
  refine ⟨⟨⟨hp, k₂, hK, hb₂⟩, slice_of k₂.dk (show 384 * L.k + (384 * L.k + 32) ≤ L.dkLen by omega_using [hdk]), ?_, hr⟩, ?_⟩
  · rw [L₁.keepBytes hP₂.b W.h₂M, L₀.keepBytes hP₁.b W.h₁M]; exact h.m
  · rw [hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h.r15]

/-! ## The key -/

/-- The end of `K-PKE.Encrypt`. -/
abbrev EncO (W : DcWf L) (σ s : State) : Prop :=
  Enc.EOut L (dcX W.toDcWfB σ) (.rbp, 384 * L.k) (dcEk L σ) (dcM' L σ) (dcG L σ).2 s

/-- At the end: `r15` as `allOk`, and the key if it is 1. -/
structure DEnd (L : Kem) (σ s : State) : Prop where
  dc : DC L σ s
  r15 : s.gpr .r15 = if allOk L.k (Enc.rhoE L (dcEk L σ)) (L.k * L.k) then 1 else 0
  key : allOk L.k (Enc.rhoE L (dcEk L σ)) (L.k * L.k) → bytesAt s.mem (pa s (.r12, 0)) 32 =
    if dcC L σ = KPke.ct L.p (aHat (Enc.rhoE L (dcEk L σ))) (dcEk L σ) (dcM' L σ) (dcG L σ).2 then (dcG L σ).1
    else dcKb L σ

/-- Before the choice of the key: what `K-PKE.Encrypt` keeps, `r15` as
`allOk`, and `c'` at `scratch + oc` if it is 1. -/
structure SelIn (L : Kem) (oc : Nat) (σ s : State) : Prop where
  pre : (decapsK L).pre σ
  k : DCK L σ s
  r15 : s.gpr .r15 = if allOk L.k (Enc.rhoE L (dcEk L σ)) (L.k * L.k) then 1 else 0
  ct : allOk L.k (Enc.rhoE L (dcEk L σ)) (L.k * L.k) → bytesAt s.mem (pa s (sc oc)) L.ctLen =
    KPke.ct L.p (aHat (Enc.rhoE L (dcEk L σ))) (dcEk L σ) (dcM' L σ) (dcG L σ).2

theorem EncO.sel {W : DcWf L} {σ s : State} (h : EncO W σ s) : SelIn L L.oCT σ s :=
  ⟨h.out.1, h.out.2, h.r15, h.ct⟩

theorem select_okD {oc : Nat} (W : DcWfB L oc) {σ : State} {s : State} (h : SelIn L oc σ s) :
    WP isa (selectAt oc L.ctLen) s (DEnd L σ) := by
  have hp := h.pre
  have k := h.k
  have L₀ := k.dc.lay W hp
  have cR : ∀ {p : Ptr} {l : Nat}, inB (dcB L) p l = true → InRegions (s.rd ++ s.wr) (pa s p) l := fun hi =>
    L₀.cR hi _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  obtain ⟨i1, i2, i3, i4, i5, s1, s2⟩ := W.sel
  refine WP.mono (select_ok W.ct.1 W.ct.2.1 W.ct.2.2.1 W.ct.2.2.2 (cR i1) (cR i2) (cR i3) (cR i4)
    (L₀.cW i5 _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩) (L₀.disj s1) (L₀.disj s2))
    fun s' ⟨hP, hb⟩ => ?_
  refine ⟨k.dc.step W hp hP.b W.selK, by rw [hP.cs .r15 (by decide)]; exact h.r15, fun ho => ?_⟩
  rw [hP.pa KeyGen.r12_cs, hb]
  exact ite_congr (propext (by rw [k.dc.c, h.ct ho])) (fun _ => k.k) (fun _ => k.kb)

theorem DEnd.hin {oc : Nat} (W : DcWfB L oc) {σ s : State} (hp : (decapsK L).pre σ) (h : DEnd L σ s) :
    ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8 := fun k hk =>
  (h.dc.lay W hp).cR (W.sv k hk) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

/-- The postcondition, from the key. -/
theorem post_of {oc : Nat} (W : DcWfB L oc) {σ s : State} (h : DEnd L σ s) {s' : State}
    (hr : (s'.gpr .rax).setWidth 32 = (s.gpr .r15).setWidth 32) (hm : s'.mem = s.mem) : (decapsK L).post σ s' := by
  have e12 : pa s (.r12, 0) = σ.gpr .rdx := by
    rw [pa, h.dc.top.regs (.r12, .rdx) (by decide), add_ofNat_zero]
  show Outcome _ _ _
  by_cases ho : allOk L.k (Enc.rhoE L (dcEk L σ)) (L.k * L.k)
  · refine .inl ⟨by rw [hr, h.r15, ifp ho]; rfl, minIterations, ?_⟩
    show decapsInternal L.p minIterations _ _ = _
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_some W.eta (a := aHat (Enc.rhoE L (dcEk L σ)))
      fun i hi j hj => aHat_eq ho hi hj, Option.map_some, hm, ← e12, h.key ho]
  · refine .inr ⟨by rw [hr, h.r15, ifn ho]; rfl, ?_⟩
    obtain ⟨i, hi, j, hj, hn⟩ := not_allOk ho
    show decapsInternal L.p minIterations _ _ = _
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_none hi hj hn]
    rfl

theorem decrypt_ok {A : Arith} (hA : ArithOk A) (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd) {σ : State}
    (hp : (decapsK L).pre σ) {s : State} (h : DC L σ s) (h15 : s.gpr .r15 = 1) : WP isa (decrypt L A) s (DM L σ) := by
  unfold decrypt
  refine WP.seq (WP.mono (seqR_ok (I := fun k => DR L k 0 σ) L.k 0 (fun k _ hk s hs => u_ok A W K hp (by omega_using [hk]) hs) s
    (DR.zero h h15)) fun s₁ h₁ => ?_)
  rw [Nat.zero_add] at h₁
  refine WP.seq (WP.mono (seqR_ok (I := fun k => DR L L.k k σ) L.k 0 (fun k _ hk s hs => s_ok hA W hp (by omega_using [hk]) hs) s₁ h₁)
    fun s₂ h₂ => ?_)
  rw [Nat.zero_add] at h₂
  exact tail_ok hA W K hp h₂

end Decaps

open Decaps in
theorem kemDecaps_correct (v : Sample4Impl) {L : Kem} (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd)
    (hctl : ctlOk (kemDecaps L v.callee) = true) (σ : State) (hp : (decapsK L).pre σ) :
    ∃ t s', Exec isa (kemDecaps L v.callee) σ t s' ∧ abiPreserved σ s' ∧ (decapsK L).post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok W.toDcWfB hp) fun s₁ ⟨h₁, h15⟩ =>
    WP.seq (WP.mono (decrypt_ok v.arith W K hp h₁ h15) fun s₂ h₂ =>
      WP.seq (WP.mono (hashes_ok W.toDcWfB hp h₂) fun s₃ h₃ =>
        WP.seq (WP.mono (Enc.encrypt_ok v K W.toKemWf (C := dcX W.toDcWfB σ) W.enc h₃.1 h₃.2) fun s₄ h₄ =>
          WP.seq (WP.mono (select_okD W.toDcWfB (EncO.sel (W := W) h₄)) fun s₅ h₅ =>
            WP.mono (topEpi_ok h₅.dc.top (h₅.hin W.toDcWfB hp)) fun s₆ ⟨hr, hg, hm⟩ =>
              (⟨hg, post_of W.toDcWfB h₅ hr hm⟩ : gprPreserved σ s₆ ∧ (decapsK L).post σ s₆))))))
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hF.1, hF.2⟩

/-! ## Constant time -/

namespace Decaps

open VG.Impl.MlKem.X86_64.Decaps

variable {L : Kem}

theorem rho_pub {σ₁ σ₂ : State} (pub : (decapsK L).pub σ₁ σ₂) : Enc.rhoE L (dcEk L σ₁) = Enc.rhoE L (dcEk L σ₂) := by
  rw [Enc.rhoE, Enc.rhoE, KPke.ekRho_dkEk, KPke.ekRho_dkEk]; exact pub.2.2.2.2.2

theorem decrypt_tr {A : Arith} (hA : ArithOk A) (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd) :
    RelCT isa (R L fun σ s => DC L σ s ∧ s.gpr .r15 = 1) (decrypt L A) fun _ _ => True := by
  unfold decrypt
  refine RelCT.seq (RelCT.mono (seqR_tr (R := fun k => R L (DR L k 0)) L.k 0
    fun k _ hk => relInv (fun σ s hp hs => u_ok A W K hp (by omega_using [hk]) hs) (u_tr A W K (by omega_using [hk])))
    (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, DR.zero h₁.1 h₁.2, DR.zero h₂.1 h₂.2⟩)
    fun _ _ h => h) ?_
  rw [Nat.zero_add]
  refine RelCT.seq (seqR_tr (R := fun k => R L (DR L L.k k)) L.k 0
    fun k _ hk => relInv (fun σ s hp hs => s_ok hA W hp (by omega_using [hk]) hs) (s_tr hA W (by omega_using [hk]))) ?_
  rw [Nat.zero_add]
  exact tail_tr hA W K

theorem hashes_trL {oc : Nat} (W : DcWfB L oc) : RelCT isa (LRel (dcR L) (dcW L)) (hashes L) fun _ _ => True := by
  unfold hashes
  exact RelCT.seq (LRel.step (dcB_bases L) (hash_tr (dcB_bases L) (ps := [(sc oM, 32), ((.rbp, 768 * L.k + 32), 32)])
      (rate := 72) (out := sc oG) (len := 64) W.h₁ (show 6 < 256 by decide)) fun x Lx =>
      WP.mono (hash_ok (dcB_bases L) (ps := [(sc oM, 32), ((.rbp, 768 * L.k + 32), 32)]) (rate := 72) (out := sc oG)
        (len := 64) W.h₁ (show 6 < 256 by decide) Lx) fun _ h => ⟨_, h.1⟩)
    (hash_tr (dcB_bases L) (ps := [((.rbp, 768 * L.k + 64), 32), ((.r14, 0), L.ctLen)]) (rate := 136) (out := sc oKB)
      (len := 32) W.h₂ (show 0x1f < 256 by decide))

theorem hashes_tr {oc : Nat} (W : DcWfB L oc) : RelCT isa (R L (DM L)) (hashes L) fun _ _ => True :=
  rel2_of (hashes_trL W) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => dc_lrel W p₁ p₂ pub h₁.dc h₂.dc

theorem EIn.any {oc : Nat} {W : DcWfB L oc} {σ : State} {E : Ptr} {ek m r : List Byte} {s : State}
    (h : Enc.EIn L (dcX W σ) E ek m r s) : Enc.EIn L (dcXA W) E ek m r s :=
  ⟨⟨σ, h.out⟩, h.ek, h.m, h.r⟩

theorem encrypt_tr (v : Sample4Impl) (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd) :
    RelCT isa (R L (EncI W.toDcWfB)) (encrypt L v.callee (.rbp, 384 * L.k)) fun _ _ => True := by
  obtain ⟨_, rhoT⟩ := W.rhoT
  refine RelCT.mono (RelCT.exists_ (P := fun ρ x y => LRel (dcR L) (dcW L) x y ∧
      Enc.EIρ L (dcXA W.toDcWfB) (.rbp, 384 * L.k) ρ x ∧ Enc.EIρ L (dcXA W.toDcWfB) (.rbp, 384 * L.k) ρ y) (Q := fun _ _ => True)
      fun ρ => RelCT.mono (Enc.encrypt_tr v K W.toKemWf (C := dcXA W.toDcWfB) W.enc rhoT (ρ := ρ)) (fun _ _ h => h)
        fun _ _ _ => trivial) ?_ fun _ _ _ => trivial
  rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
  have i₁ : Enc.EIρ L (dcXA W.toDcWfB) (.rbp, 384 * L.k) (Enc.rhoE L (dcEk L σ₁)) x := ⟨_, _, _, rfl, EIn.any h₁.1, h₁.2⟩
  have i₂ : Enc.EIρ L (dcXA W.toDcWfB) (.rbp, 384 * L.k) (Enc.rhoE L (dcEk L σ₁)) y :=
    ⟨_, _, _, (rho_pub pub).symm, EIn.any h₂.1, h₂.2⟩
  exact ⟨Enc.rhoE L (dcEk L σ₁), dc_lrel W.toDcWfB p₁ p₂ pub h₁.1.out.2.dc h₂.1.out.2.dc, i₁, i₂⟩

theorem select_tr {oc : Nat} (W : DcWfB L oc) :
    RelCT isa (R L (SelIn L oc)) (selectAt oc L.ctLen) fun _ _ => True := by
  obtain ⟨_, selT⟩ := W.selT
  exact rel2_of (Q := LRel (dcR L) (dcW L)) (taintRel [.rbx, .r12, .r14] (fun _ _ h =>
    fa3 (h.eq (p := sc 0) (l := 1) W.inBs.1) (h.eq (p := (.r12, 0)) (l := 1) W.inBs.2.1)
      (h.eq (p := (.r14, 0)) (l := 1) W.inBs.2.2)) selT)
    fun _ _ _ _ p₁ p₂ pub h₁ h₂ => dc_lrel W p₁ p₂ pub h₁.k.dc h₂.k.dc

theorem pro_tr : RelCT isa (R L fun σ s => s = σ) (.block pro) fun _ _ => True :=
  taintRel [.rcx, .rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ => by
    subst h₁ h₂
    exact fa4 pub.2.2.2.1 pub.1 pub.2.1 pub.2.2.1) (by taint_decide)

theorem epi_tr : RelCT isa (R L (DEnd L)) (.block topEpi) fun _ _ => True :=
  taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.dc.top.regs (.rbx, .rcx) (by decide), h₂.dc.top.regs (.rbx, .rcx) (by decide), pub.2.2.2.1])
    (by taint_decide)

end Decaps

open Decaps in
theorem kemDecaps_ct (v : Sample4Impl) {L : Kem} (W : DcWf L) {wc wd : List Nat} (K : KemCalls L wc wd) :
    ConstantTime isa (decapsK L).pre (decapsK L).pub (kemDecaps L v.callee) := by
  refine relStart (Q := fun _ _ => True) ?_
  unfold kemDecaps
  refine RelCT.seq (relInv (I' := fun σ s => DC L σ s ∧ s.gpr .r15 = 1)
    (fun σ s hp hs => by subst hs; exact pro_ok W.toDcWfB hp) pro_tr) ?_
  refine RelCT.seq (relInv (I' := DM L) (fun σ s hp hs => decrypt_ok v.arith W K hp hs.1 hs.2)
    (decrypt_tr v.arith W K)) ?_
  refine RelCT.seq (relInv (I' := EncI W.toDcWfB) (fun σ s hp hs => hashes_ok W.toDcWfB hp hs) (hashes_tr W.toDcWfB)) ?_
  refine RelCT.seq (relInv (I' := EncO W) (fun σ s _ hs => Enc.encrypt_ok v K W.toKemWf (C := dcX W.toDcWfB σ) W.enc hs.1 hs.2)
    (encrypt_tr v W K)) ?_
  refine RelCT.seq (relInv (I' := DEnd L) (fun σ s _ hs => select_okD W hs.sel)
    (RelCT.mono (select_tr W.toDcWfB) (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, h₁.sel, h₂.sel⟩)
      fun _ _ h => h)) ?_
  exact RelCT.mono epi_tr (fun _ _ h => h) fun _ _ _ => trivial

end VG.Proof.MlKem.X86_64
