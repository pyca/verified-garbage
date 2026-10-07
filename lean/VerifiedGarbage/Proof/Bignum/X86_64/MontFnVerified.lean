import VerifiedGarbage.Proof.Bignum.X86_64.MontFnBase
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Spec.Rsa.Mont
import VerifiedGarbage.Proof.Framework.Contract

namespace VG.Proof.Bignum.X86_64.MontFn

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.Bignum VG.Impl.Bignum.X86_64.MontFn
open VG.Impl.Bignum.X86_64.Public (aN aAcc aTmp)
open VG.Spec.Rsa.Mont (numAt wOf wordAt Layout Operand Keeps arrAt aM minvWord)

/-- The index in the low half of `r`. -/
abbrev idx (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- `vg_rsa_mont_mul(ws = rdi, ws_len = rsi, o = edx, a = ecx, b = r8d)`. -/
def fnContract : Contract isa where
  pre s :=
    let ws := s.gpr .rdi
    let n := (s.gpr .rsi).toNat
    let w := wOf s.mem ws
    s.rd = [] ∧ s.wr = [⟨ws, n * 8⟩] ∧ (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨ws, n * 8⟩ ∧
      ws.toNat + n * 8 ≤ 2 ^ 64 ∧ Layout s.mem ws n ∧ Operand (idx s .rdx) ∧ Operand (idx s .rcx) ∧
      Operand (idx s .r8) ∧
      ((s.mem.readW (ws + BitVec.ofNat 64 (arrAt w aM)) 64).toNat * (wordAt s.mem ws minvWord).toNat + 1) %
        2 ^ 64 = 0 ∧
      numAt s.mem ws w (idx s .r8) < numAt s.mem ws w aM
  post s s' :=
    let ws := s.gpr .rdi
    let w := wOf s.mem ws
    let M := numAt s.mem ws w aM
    numAt s'.mem ws w (idx s .rdx) < M ∧
      numAt s'.mem ws w (idx s .rdx) * 2 ^ (64 * w) % M = numAt s.mem ws w (idx s .rcx) * numAt s.mem ws w (idx s .r8) % M ∧
      Keeps ws (s.gpr .rsi).toNat w (idx s .rdx) s.mem s'.mem
  pub s₁ s₂ :=
    s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
      (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32 ∧ (s₁.gpr .rcx).setWidth 32 = (s₂.gpr .rcx).setWidth 32 ∧
      (s₁.gpr .r8).setWidth 32 = (s₂.gpr .r8).setWidth 32 ∧ wOf s₁.mem (s₁.gpr .rdi) = wOf s₂.mem (s₂.gpr .rdi)

/-- The words of a working space of `w = 2` at `0x1000`: the header, then the
modulus 1 in array 0 and zeros. -/
def satWord (k : Nat) : BitVec 64 :=
  if k = 6 then 2 else if k = 7 then 0xFFFFFFFFFFFFFFFF else if 8 ≤ k ∧ k < 16 then BitVec.ofNat 64 (0x1100 + (k - 8) * 32)
  else if k = 32 then 1 else 0

def satMem : Mem := fun x =>
  let i := (x - 0x1000).toNat
  if i < 512 then (satWord (i / 8)).extractLsb' (8 * (i % 8)) 8 else 0

/-- A state meeting `mulContract`: `w = 2`, the working space at `0x1000`, `o = a = b = 1`. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 1 | .rcx => 1 | .r8 => 1 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := []
  wr := [⟨0x1000, 512⟩]

theorem fn_implies : fnContract.Implies (Spec.Rsa.Mont.mulContract abi) where
  pre := by sig_implies_pre [Spec.Rsa.Mont.mulContract, Spec.Rsa.Mont.sig, fnContract, abi, argRegs]
  post := by sig_implies_post [Spec.Rsa.Mont.mulContract, Spec.Rsa.Mont.sig, fnContract, abi, argRegs]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.Mont.mulContract, Spec.Rsa.Mont.sig, fnContract, abi, argRegs] at h
    obtain ⟨hsp, hw, hdi, hsi, hdx, hcx, h8⟩ := h
    exact ⟨hsp, hdi, hsi, hdx, hcx, h8, List.singleton_inj.mp hw⟩
  sat := by sig_implies_sat [Spec.Rsa.Mont.mulContract, Spec.Rsa.Mont.sig, fnContract, abi, argRegs] [satState] using satState

/-- The `k` words at offset `d` of `B` are the `8 k` bytes there. -/
theorem read_eq_wv (m : Mem) (B : Addr) (d : Nat) : ∀ k, (m.read (off B d) (8 * k)).toNat = wv m B d k
  | 0 => by simp [Mem.read, wv]
  | k + 1 => by
    rw [show 8 * (k + 1) = 8 + 8 * k by omega, Proof.Mont.read_toNat_add, read_eq_wv m B d k, wv,
      Offset.add_add, show 8 * (8 * k) = 64 * k by omega]
    congr 2

theorem numAt_eq (m : Mem) (B : Addr) (w j : Nat) : numAt m B w j = wv m B (slot w j) w := by
  rw [← read_eq_wv]; rfl

theorem idx_eq (s : State) (r : Reg) : (s.gpr r).setWidth 32 = BitVec.ofNat 32 (idx s r) := by
  apply BitVec.eq_of_toNat_eq; simp [idx]

/-- What `fnContract.pre` gives the proofs: the working space, its header and the arguments. -/
theorem fn_good {s : State} (h : fnContract.pre s) :
    Scr s (s.gpr .rdi) ((s.gpr .rsi).toNat * 8) ∧
    Hdr s.mem (s.gpr .rdi) (wOf s.mem (s.gpr .rdi)) (wordAt s.mem (s.gpr .rdi) minvWord) ∧
    slot (wOf s.mem (s.gpr .rdi)) 8 ≤ (s.gpr .rsi).toNat * 8 ∧ 2 ≤ wOf s.mem (s.gpr .rdi) ∧
    wOf s.mem (s.gpr .rdi) < 2 ^ 31 := by
  obtain ⟨-, hwr, -, hnw, ⟨h2, h31, h8, harr⟩, -⟩ := h
  refine ⟨Scr.of_mem (by rw [hwr]; simp) hnw, ⟨?_, rfl, fun j hj => harr j hj⟩, by
    simp only [slot, hdrBytes, Spec.Rsa.Mont.arrAt, Spec.Rsa.Mont.hdrBytes] at h8 ⊢; omega, h2, h31⟩
  simp [word, wOf, wordAt, Spec.Rsa.Mont.wWord, sW, off]

theorem fn_correct (s : State) (h : fnContract.pre s) :
    ∃ t s', Exec isa mulBase s t s' ∧ abiPreserved s s' ∧ fnContract.post s s' := by
  obtain ⟨hs, hH, hZ, hw, hw'⟩ := fn_good h
  obtain ⟨-, hwr, hret, hnw, -, ⟨ho, ho2, ho3⟩, ⟨ha, ha2, ha3⟩, ⟨hb, hb2, hb3⟩, hinv, hB⟩ := h
  suffices hwp : WP isa mulBase s fun s' => gprPreserved s s' ∧ fnContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hg, hp⟩
  rw [numAt_eq, numAt_eq] at hB
  refine WP.mono (mulBase_ok hs rfl hH hZ hw hw' ho ha hb ho2 ho3 ha2 hb2 (idx_eq s .rdx) (idx_eq s .rcx)
    (idx_eq s .r8) hinv hB) fun t ⟨hlt, heq, har, k, hcs⟩ => ?_
  have hn := hs.nowrap
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hcs _ (by simp)
    · exact hcs _ (by simp)
    · exact k.gpr (by decide)
    all_goals exact hcs _ (by simp)
  · refine Mem.readW_congr fun i hi => har _ fun j hj => Or.inr ?_
    have hx := hret (s.gpr .rsp + BitVec.ofNat 64 i) (by
      simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
    simp only [Region.Contains, Nat.not_le] at hx
    have := slot_le (w := wOf s.mem (s.gpr .rdi)) (show j < 8 by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; rcases hj with rfl | rfl | rfl <;> first | decide | omega)
    simp only [ofs]; omega
  · rw [numAt_eq, numAt_eq]; exact hlt
  · rw [numAt_eq, numAt_eq, numAt_eq, numAt_eq]; exact heq
  · intro i hi hj
    have := har (s.gpr .rdi + BitVec.ofNat 64 i) fun j hj' => by
      rw [show ofs (s.gpr .rdi) (s.gpr .rdi + BitVec.ofNat 64 i) = i by
        simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega)]]
      exact hj j hj'
    exact this

/-! ## Constant time -/

/-- The public data of a run: the working space, its size, `w` and the indices. -/
structure FnData where
  B : Addr
  Z : Nat
  w : Nat
  o : Nat
  a : Nat
  b : Nat

def FnPhi (d : FnData) (s : State) : Prop :=
  fnContract.pre s ∧ s.gpr .rdi = d.B ∧ (s.gpr .rsi).toNat * 8 = d.Z ∧ wOf s.mem d.B = d.w ∧
    idx s .rdx = d.o ∧ idx s .rcx = d.a ∧ idx s .r8 = d.b

def FnBases (d : FnData) (t : State) : Prop := BasesL aN aAcc aTmp d.o d.a d.b ⟨d.B, d.Z, d.w⟩ t

theorem pins_fnBases : Pins FnBases [.rbx, .r11, .r9, .r10, .r8, .r12, .rsi] := by
  intro d s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁, g₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂, g₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]
  · rw [e₁, e₂]
  · rw [f₁, f₂]
  · rw [g₁, g₂]

theorem wp_conj {c : Prog isa} {s : State} {P Q : State → Prop} (h₁ : WP isa c s P) (h₂ : WP isa c s Q) :
    WP isa c s fun t => P t ∧ Q t := by
  obtain ⟨t, s', e, p⟩ := h₁
  obtain ⟨t', s'', e', q⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact ⟨t, s', e, p, q⟩

theorem zext_ok (s : State) :
    WP isa (.block zext) s fun t => t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rdx = ((s.gpr .rdx).setWidth 32).setWidth 64 ∧
      t.gpr .rcx = ((s.gpr .rcx).setWidth 32).setWidth 64 ∧ t.gpr .r8 = ((s.gpr .r8).setWidth 32).setWidth 64 := by
  unfold zext; xrun

/-- After `zext`: the rest of the head runs to the bases, and the
registers it addresses with are public. -/
def FnZext (d : FnData) (t : State) : Prop :=
  WP isa (.block (saves ++ basesR)) t (FnBases d) ∧ t.gpr .rdi = d.B ∧
    t.gpr .rdx = (BitVec.ofNat 32 d.o).setWidth 64 ∧ t.gpr .rcx = (BitVec.ofNat 32 d.a).setWidth 64 ∧
    t.gpr .r8 = (BitVec.ofNat 32 d.b).setWidth 64

theorem pins_fnZext : Pins FnZext [.rdi, .rdx, .rcx, .r8] := by
  intro d s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  obtain ⟨-, a₁, b₁, c₁, d₁⟩ := h₁
  obtain ⟨-, a₂, b₂, c₂, d₂⟩ := h₂
  rcases hr with rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]

theorem fn_rel : RelCT isa (Two FnPhi) mulBase fun _ _ => True := by
  unfold mulBase
  rw [show enter ++ basesR = zext ++ (saves ++ basesR) from rfl]
  refine RelCT.seq (RelCT.block_append (RelCT.seq (two_post (Ψ := FnZext)
    (two_taint [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide)) fun d s h => ?_)
    (two_post (two_taint _ pins_fnZext (by taint_decide)) fun _ _ h => h.1)))
    (two_taint _ pins_fnBases (by taint_decide))
  obtain ⟨hp, hdi, -, hw, ho, ha, hb⟩ := h
  obtain ⟨hs, hH, hZ8, -, -⟩ := fn_good hp
  obtain ⟨-, -, -, -, -, ⟨ho8, -⟩, ⟨ha8, -⟩, ⟨hb8, -⟩, -⟩ := hp
  have hhead := fnHead_ok hs rfl hH hZ8 ho8 ha8 hb8 (idx_eq s .rdx) (idx_eq s .rcx) (idx_eq s .r8)
  rw [show enter ++ basesR = zext ++ (saves ++ basesR) from rfl, WP.block_append_iff] at hhead
  refine WP.mono (wp_conj hhead (zext_ok s)) fun t ⟨hw', h1, h2, h3, h4⟩ => ⟨WP.mono hw' ?_, ?_, ?_, ?_, ?_⟩
  · rintro u ⟨u1, u2, u3, u4, u5, u6, -, u8, -⟩
    obtain ⟨B, Z, w, o, a, b⟩ := d
    simp only at hdi hw ho ha hb ⊢
    subst hdi hw ho ha hb
    exact ⟨u1, u2, u3, u4, u5, u6, u8⟩
  · rw [h1, hdi]
  · rw [h2, idx_eq s .rdx, ho]
  · rw [h3, idx_eq s .rcx, ha]
  · rw [h4, idx_eq s .r8, hb]

theorem fn_ct : ConstantTime isa fnContract.pre fnContract.pub mulBase :=
  RelCT.constantTime (fn_rel.mono (fun s₁ s₂ ⟨h₁, h₂, hsp, hdi, hsi, hdx, hcx, h8, hw⟩ =>
    ⟨⟨s₁.gpr .rdi, (s₁.gpr .rsi).toNat * 8, wOf s₁.mem (s₁.gpr .rdi), idx s₁ .rdx, idx s₁ .rcx, idx s₁ .r8⟩,
      ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      ⟨h₂, hdi.symm, by rw [hsi], (congrArg (wOf s₂.mem) hdi).trans hw.symm, by simp only [idx, hdx], by simp only [idx, hcx],
        by simp only [idx, h8]⟩⟩) fun _ _ h => h)

/-- `vg_rsa_mont_mul` on x86-64. -/
theorem fn_verified : Verified target mulBase (Spec.Rsa.Mont.mulContract abi) :=
  Verified.of_correct fn_correct fn_ct fn_implies

end VG.Proof.Bignum.X86_64.MontFn
