module

public import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Sign
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Glue
public import VerifiedGarbage.Proof.MlDsa.Sign.Leak
public import VerifiedGarbage.Spec.MlDsa.PreparedKey
import VerifiedGarbage.Proof.MlKem.X86_64.Rel
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Keccak
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.MlKem.Mem

/-! ### `MlDsa.X86_64.Sign.Hash`, which this module and modules that import it used -/

section

/-!
# ML-DSA signing on x86-64: `H` of pieces of memory

`shakeAt ps out len` zeroes the Keccak state, absorbs the pieces `ps`, pads
and squeezes `len` bytes to `out`: `H` of their concatenation (`shake_ok`),
leaking only the addresses (`shake_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt stateAt rates absorb pad squeezeFrom Repr)

/-- The state after absorbing `m` padded with `suffix`, for the rate `rate`. -/
abbrev padded (rate : Nat) (suffix : Byte) (m : List Byte) : Spec.Sha3.State := absorb rate (pad rate suffix m)

theorem squeezeFrom_zero (rate : Nat) (S : Spec.Sha3.State) (d : Nat) :
    squeezeFrom rate S 0 d = Spec.Sha3.squeeze rate S d := by
  simp only [squeezeFrom, Spec.Sha3.squeeze, Nat.zero_add, List.drop_zero]

/-- `H(s, d) = SHAKE256(s, 8d)`: rate 136, suffix `0x1f`. -/
theorem H_eq (m : List Byte) (d : Nat) : H m d = squeezeFrom 136 (padded 136 (BitVec.ofNat 8 0x1f) m) 0 d := by
  rw [squeezeFrom_zero]; rfl

/-- The all-zero state represents the empty message. -/
theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) : Repr mem p rate [] := by
  show stateAt mem p = Proof.Sha3.Rep rate []
  rw [Proof.Sha3.rep_nil, h]

/-- A piece of the message: absorbed as `vg_keccak_absorb` needs, its register kept by the calls. -/
def pieceChk (bs : List (Reg × Nat)) (p : Ptr × Nat) : Bool :=
  kabsChk bs p.1 p.2 && decide (p.1.1 ∈ bases)

/-- The bytes of the pieces, concatenated. -/
abbrev pieces (s : State) (ps : List (Ptr × Nat)) : List Byte := ps.flatMap fun p => bytesAt s.mem (pa s p.1) p.2

theorem pieces_length (s : State) (ps : List (Ptr × Nat)) : (pieces s ps).length = totLen ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [pieces, List.flatMap_cons, List.length_append, VG.Proof.MlKem.bytesAt_length] at ih ⊢
    rw [ih]; simp [totLen]

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

theorem pieceChk_keep {p : Ptr × Nat} (h : pieceChk (rbs ++ wbs) p = true) :
    keepB (rbs ++ wbs) [(sc 0, 200), (sc 200, 640)] p.1 p.2 = true := by
  simp only [pieceChk, kabsChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hin, _⟩, _⟩, _⟩, s1⟩, s2⟩, hcs⟩ := h
  simp only [keepB, List.all_cons, List.all_nil, s1, s2, hin, decide_eq_true hcs, Bool.and_self]

theorem pieces_keep {s s' : State} (L : Lay D rbs wbs s) {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) :
    ∀ {ps : List (Ptr × Nat)}, (∀ p ∈ ps, keepB (rbs ++ wbs) ws p.1 p.2 = true) → pieces s' ps = pieces s ps
  | [], _ => rfl
  | p :: ps, h => by
    simp only [pieces, List.flatMap_cons]
    rw [L.keepBytes hP (h p (List.mem_cons_self ..))]
    exact congrArg _ (pieces_keep L hP fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem hcs_trans {s s₁ s₂ : State} (h₁ : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r)
    (h₂ : ∀ r ∈ calleeSaved, s₂.gpr r = s₁.gpr r) : ∀ r ∈ calleeSaved, s₂.gpr r = s.gpr r :=
  fun r hr => (h₂ r hr).trans (h₁ r hr)

theorem bases_all : ∀ w ∈ [((sc 0 : Ptr), 200), ((sc 200 : Ptr), 640)], w.1.1 ∈ bases := by
  decide

/-- What absorbing the pieces `ps` from position `pos` does. -/
def AbsOk (D : Nat) (rbs wbs : List (Reg × Nat)) (rate : Nat) (ps : List (Ptr × Nat)) : Prop :=
  ∀ (s : State) (_ : Lay D rbs wbs s) (pos : Nat) (msg : List Byte),
    ps.all (pieceChk (rbs ++ wbs)) = true → pos < rate → pos = msg.length % rate →
    Repr s.mem (pa s (sc 0)) rate msg →
    WP isa (absAll rate ps pos) s fun s' => PPostB D s s' [(sc 0, 200), (sc 200, 640)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ Repr s'.mem (pa s (sc 0)) rate (msg ++ pieces s ps)

theorem absAll_ok (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) (hD : 24 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {rate : Nat} (hrate : rate ∈ rates) : ∀ (ps : List (Ptr × Nat)), AbsOk D rbs wbs rate ps
  | [] => fun _ _ _ _ _ _ _ hR => WP.block_nil ⟨PostB.refl _ _ _, fun _ _ => rfl, by simpa using hR⟩
  | (p, l) :: ps => by
    intro s L pos msg hps hpos hm hR
    simp only [List.all_cons, Bool.and_eq_true] at hps
    have hkc : kabsChk (rbs ++ wbs) p l = true := by
      simp only [pieceChk, Bool.and_eq_true] at hps; exact hps.1.1
    have hr0 : 0 < rate := Nat.lt_of_le_of_lt (Nat.zero_le _) hpos
    rw [absAll]
    refine WP.seq (WP.mono (kabs_ok L hD hk hkc hrate hpos) fun s₁ ⟨hP₁, hc₁, hR₁⟩ => ?_)
    have L₁ := L.post hP₁ hcs
    have e0 : pa s₁ (sc 0) = pa s (sc 0) := hP₁.pa (by decide)
    have hR₁' := hR₁ msg hR hm
    rw [← e0] at hR₁'
    have h3 : ((pos + l) % rate) = (msg ++ bytesAt s.mem (pa s p) l).length % rate := by
      rw [List.length_append, VG.Proof.MlKem.bytesAt_length, hm, Nat.mod_add_mod]
    refine WP.mono (absAll_ok hcs hD hk hrate ps s₁ L₁ ((pos + l) % rate) (msg ++ bytesAt s.mem (pa s p) l) hps.2
      (Nat.mod_lt _ hr0) h3 hR₁') fun s₂ ⟨hP₂, hc₂, hR₂⟩ =>
        ⟨PPostB.trans hP₁ hP₂ bases_all (fun w hw => hw) (fun w hw => hw), hcs_trans hc₁ hc₂, ?_⟩
    rw [e0, pieces_keep L hP₁ fun q hq => pieceChk_keep (List.all_eq_true.mp hps.2 q hq)] at hR₂
    simpa only [pieces, List.flatMap_cons, List.append_assoc] using hR₂

/-- The output: `len` bytes to `out`. -/
def shakeChk (bs wbs : List (Reg × Nat)) (ps : List (Ptr × Nat)) (out : Ptr) (len : Nat) : Bool :=
  kChk bs wbs && ps.all (pieceChk bs) && ksqzChk bs wbs out len

theorem shakeChk_spec {bs wbs : List (Reg × Nat)} {ps : List (Ptr × Nat)} {out : Ptr} {len : Nat}
    (h : shakeChk bs wbs ps out len = true) :
    kChk bs wbs = true ∧ ps.all (pieceChk bs) = true ∧ ksqzChk bs wbs out len = true := by
  simp only [shakeChk, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem shake_ok (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) (hD : 24 ≤ D) {ps : List (Ptr × Nat)} {out : Ptr}
    {len : Nat} (hc : shakeChk (rbs ++ wbs) wbs ps out len = true) {s : State} (L : Lay D rbs wbs s) :
    WP isa (shakeAt ps out len) s fun s' => PPostB D s s' [(sc 0, 200), (sc 200, 640), (out, len)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ bytesAt s'.mem (pa s out) len = H (pieces s ps) len := by
  obtain ⟨hk, hps, hsq⟩ := shakeChk_spec hc
  have hocs : out.1 ∈ bases := by
    simp only [ksqzChk, Bool.and_eq_true, decide_eq_true_eq] at hsq; exact hsq.1.1.1.1.2
  have hrate : (136 : Nat) ∈ rates := by decide
  refine WP.seq (WP.mono (kzero_ok L hk) fun s₁ ⟨hP₁, hc₁, hz⟩ => ?_)
  have L₁ := L.post hP₁ hcs
  have e1 : pa s₁ (sc 0) = pa s (sc 0) := hP₁.pa (by decide)
  have hpk : ∀ p ∈ ps, keepB (rbs ++ wbs) [(sc 0, 200)] p.1 p.2 = true := fun p hp => by
    have := pieceChk_keep (List.all_eq_true.mp hps p hp)
    simp only [keepB, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true] at this ⊢
    exact ⟨this.1, this.2.1⟩
  have epc : pieces s₁ ps = pieces s ps := pieces_keep L hP₁ hpk
  refine WP.seq (WP.mono (absAll_ok hcs hD hk hrate ps s₁ L₁ 0 [] hps (by decide) rfl
    (by rw [e1]; exact repr_nil hz)) fun s₂ ⟨hP₂, hc₂, hR₂⟩ => ?_)
  have L₂ := L₁.post hP₂ hcs
  have e2 : pa s₂ (sc 0) = pa s₁ (sc 0) := hP₂.pa (by decide)
  rw [List.nil_append, epc] at hR₂
  refine WP.seq (WP.mono (kpad_ok L₂ hD hk hrate (pos := totLen ps % 136) (Nat.mod_lt _ (by decide))
    (show 0x1f < 256 by decide)) fun s₃ ⟨hP₃, hc₃, hS₃⟩ => ?_)
  have L₃ := L₂.post hP₃ hcs
  have e3 : pa s₃ (sc 0) = pa s₂ (sc 0) := hP₃.pa (by decide)
  have hS := hS₃ (pieces s ps) (by rw [e2]; exact hR₂) (by rw [pieces_length])
  refine WP.mono (ksqz_ok L₃ hD hk hsq hrate) fun s₄ ⟨hP₄, hc₄, ho⟩ => ?_
  have eo : pa s₃ out = pa s out := by rw [hP₃.pa hocs, hP₂.pa hocs, hP₁.pa hocs]
  have h12 : PPostB D s s₂ [(sc 0, 200), (sc 200, 640)] :=
    PPostB.trans hP₁ hP₂ bases_all (fun w hw => by rw [List.mem_singleton] at hw; subst hw; exact List.mem_cons_self ..)
      (fun w hw => hw)
  have h123 : PPostB D s s₃ [(sc 0, 200), (sc 200, 640)] := PPostB.trans h12 hP₃ bases_all (fun w hw => hw) (fun w hw => hw)
  have hcs4 : ∀ w ∈ [((sc 0 : Ptr), 200), (out, len), ((sc 200 : Ptr), 640)], w.1.1 ∈ bases := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    exacts [by decide, hocs, by decide]
  refine ⟨PPostB.trans h123 hP₄ hcs4 (fun w hw => ?_) (fun w hw => ?_),
    hcs_trans (hcs_trans (hcs_trans hc₁ hc₂) hc₃) hc₄, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h <;> simp [h]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with h | h | h <;> simp [h]
  rw [← eo, ho, e3, hS, H_eq]

/-! ## Constant time -/

theorem LRel.step (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {c : Prog isa}
    (htr : RelCT isa (LRel D rbs wbs) c fun _ _ => True)
    (hok : ∀ x, Lay D rbs wbs x → WP isa c x fun x' => ∃ W, PostB D x x' W) :
    RelCT isa (LRel D rbs wbs) c (LRel D rbs wbs) :=
  VG.Proof.MlKem.X86_64.RelCT.postDep htr (F := fun x x' => ∃ W, PostB D x x' W) (fun x y h => ⟨hok x h.lx, hok y h.ly⟩)
    fun _ _ _ _ h ⟨_, hx⟩ ⟨_, hy⟩ => h.post hcs hx hy

theorem nil_tr {P : State → State → Prop} : RelCT isa P (.block []) P :=
  VG.Proof.MlKem.X86_64.RelCT.postDep (block_nomem_tr fun _ hi => absurd hi List.not_mem_nil)
    (F := fun x x' => x' = x) (fun _ _ _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) fun _ _ _ _ h hx hy => hx ▸ hy ▸ h

theorem absAll_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) (hD : 24 ≤ D) (hk : kChk (rbs ++ wbs) wbs = true)
    {rate : Nat} (hrate : rate ∈ rates) :
    ∀ (ps : List (Ptr × Nat)) (pos : Nat), ps.all (pieceChk (rbs ++ wbs)) = true → pos < rate →
      RelCT isa (LRel D rbs wbs) (absAll rate ps pos) (LRel D rbs wbs)
  | [], _, _, _ => nil_tr
  | (p, l) :: ps, pos, hps, hpos => by
    simp only [List.all_cons, Bool.and_eq_true] at hps
    have hkc : kabsChk (rbs ++ wbs) p l = true := by
      simp only [pieceChk, Bool.and_eq_true] at hps; exact hps.1.1
    have hr0 : 0 < rate := Nat.lt_of_le_of_lt (Nat.zero_le _) hpos
    rw [absAll]
    exact RelCT.seq (LRel.step hcs (kabs_tr hD hk hkc hrate hpos)
      fun x Lx => WP.mono (kabs_ok Lx hD hk hkc hrate hpos) fun _ h => ⟨_, h.1⟩)
      (absAll_tr hcs hD hk hrate ps ((pos + l) % rate) hps.2 (Nat.mod_lt _ hr0))

theorem shake_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) (hD : 24 ≤ D) {ps : List (Ptr × Nat)} {out : Ptr}
    {len : Nat} (hc : shakeChk (rbs ++ wbs) wbs ps out len = true) :
    RelCT isa (LRel D rbs wbs) (shakeAt ps out len) (LRel D rbs wbs) := by
  obtain ⟨hk, hps, hsq⟩ := shakeChk_spec hc
  have hrate : (136 : Nat) ∈ rates := by decide
  have i0 : inB (rbs ++ wbs) (sc 0) 200 = true := (kChk_spec hk).2.2.1
  refine RelCT.seq (LRel.step hcs (kzero_tr fun x y h => h.eq i0)
    fun x Lx => WP.mono (kzero_ok Lx hk) fun _ h => ⟨_, h.1⟩)
    (RelCT.seq (absAll_tr hcs hD hk hrate ps 0 hps (by decide)) (RelCT.seq (LRel.step hcs
      (kpad_tr hD hk hrate (Nat.mod_lt _ (by decide)) (show 0x1f < 256 by decide))
      fun x Lx => WP.mono (kpad_ok Lx hD hk hrate (Nat.mod_lt _ (by decide)) (show 0x1f < 256 by decide))
        fun _ h => ⟨_, h.1⟩)
      (LRel.step hcs (ksqz_tr hD hk hsq hrate) fun x Lx => WP.mono (ksqz_ok Lx hD hk hsq hrate) fun _ h => ⟨_, h.1⟩)))

end

end VG.Proof.MlDsa.X86_64.Sign

end

end

/-!
# ML-DSA signing on x86-64: the function's contract, layout, entry and exit

The contract the proof is written against (`signK`, which the shared contract
implies), the layout of the function's buffers (`sk`, `mu`, `rnd` read, in
`rbp`, `r12`, `r13`; `scratch` and `sig` written, in `rbx` and `r14`), what
holds of the state throughout (`Top`: the permissions and the stack pointer of
entry, the pointers in their registers, the caller's callee-saved registers
saved in `scratch`, and the return address), the saves (`pro_ok`), the return
(`topEpi_ok`), branches on `r15` (`ifOkElse_ok`, `ifOkElse_tr`) and sequences
of pieces indexed by a number (`seqR_ok`, `seqR_tr`), and of pieces that stop
at the first that leaves `r15 = 0` (`seqOk_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The contract -/

/-- The size of `scratch` in bytes. -/
abbrev scrLen (p : Params) : Nat := 8 * scratchWords p

/-- The length of the key at `rdi`: the encoded key, or, if the flag `r9` is
set, a prepared key (`PreparedSecretKey`), which begins with it. -/
abbrev skL (p : Params) (s : State) : Nat := if s.gpr .r9 = 0 then p.skLen else preparedSecretKeyBytes p

theorem skLen_le_skL (p : Params) (s : State) : p.skLen ≤ skL p s := by
  unfold skL preparedSecretKeyBytes; split <;> omega_using []

/-- `vg_mldsa*_sign_with_cache(sk = rdi, mu = rsi, rnd = rdx, sig = rcx, scratch = r8,
prepared = r9) -> eax`, with `D` bytes of stack, and the leakage `signLeak`: signing
with the encoded key at `sk`, which, if `prepared ≠ 0`, is a prepared key (`skL`). -/
def signK (p : Params) (D : Nat) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, skL p s⟩, ⟨s.gpr .rsi, 64⟩, ⟨s.gpr .rdx, 32⟩] ∧
    s.wr = [⟨s.gpr .rcx, p.sigLen⟩, ⟨s.gpr .r8, scrLen p⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, skL p s⟩ ⟨s.gpr .rcx, p.sigLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, skL p s⟩ ⟨s.gpr .r8, scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, 64⟩ ⟨s.gpr .rcx, p.sigLen⟩ ∧ Region.Disjoint ⟨s.gpr .rsi, 64⟩ ⟨s.gpr .r8, scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .rcx, p.sigLen⟩ ∧ Region.Disjoint ⟨s.gpr .rdx, 32⟩ ⟨s.gpr .r8, scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rcx, p.sigLen⟩ ⟨s.gpr .r8, scrLen p⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, skL p s⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, 64⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, p.sigLen⟩ ∧
    (retR s).Disjoint ⟨s.gpr .r8, scrLen p⟩ ∧
    (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .rdi, skL p s⟩ ∧ (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .rsi, 64⟩ ∧
    (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .rdx, 32⟩ ∧ (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .rcx, p.sigLen⟩ ∧
    (below (s.gpr .rsp) D).Disjoint ⟨s.gpr .r8, scrLen p⟩ ∧
    (s.gpr .rdi).toNat + skL p s ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + p.sigLen ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + scrLen p ≤ 2 ^ 64 ∧
    D ≤ (s.gpr .rsp).toNat ∧
    (s.gpr .r9 ≠ 0 → PreparedSecretKey p s.mem (s.gpr .rdi))
  post s s' :=
    Outcome (fun b => signMu p b (bytesAt s.mem (s.gpr .rdi) p.skLen) (bytesAt s.mem (s.gpr .rsi) 64)
      (bytesAt s.mem (s.gpr .rdx) 32)) ((s'.gpr .rax).setWidth 32) (bytesAt s'.mem (s.gpr .rcx) p.sigLen)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    signLeak p (bytesAt s₁.mem (s₁.gpr .rdi) p.skLen) (bytesAt s₁.mem (s₁.gpr .rsi) 64)
        (bytesAt s₁.mem (s₁.gpr .rdx) 32) =
      signLeak p (bytesAt s₂.mem (s₂.gpr .rdi) p.skLen) (bytesAt s₂.mem (s₂.gpr .rsi) 64)
        (bytesAt s₂.mem (s₂.gpr .rdx) 32) ∧
    s₁.gpr .r9 = s₂.gpr .r9

/-! ## The layout -/

theorem contains_prefix {a : Addr} {n k : Nat} (h : n ≤ k) : (⟨a, k⟩ : Region).Contains a n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact h

/-- `sk`, `mu` and `rnd`. -/
abbrev sgR (p : Params) : List (Reg × Nat) := [(.rbp, p.skLen), (.r12, 64), (.r13, 32)]
/-- `scratch` and `sig`. -/
abbrev sgW (p : Params) : List (Reg × Nat) := [(.rbx, scrLen p), (.r14, p.sigLen)]
abbrev sgB (p : Params) : List (Reg × Nat) := sgR p ++ sgW p

/-- The pointers the function keeps, and the registers they arrive in. -/
abbrev sgM : List (Reg × Reg) := [(.rbx, .r8), (.rbp, .rdi), (.r12, .rsi), (.r13, .rdx), (.r14, .rcx)]

theorem sgB_bases (p : Params) : ∀ b ∈ sgB p, b.1 ∈ bases := by
  intro b hb; simp only [sgB, sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
theorem sgM_bases : ∀ m ∈ sgM, m.1 ∈ bases := by decide

/-- The register saved at `scratch + 840 + 8k`. -/
abbrev savedReg (k : Nat) : Reg := savedRegs.getD k .rbx

/-- What holds throughout the function entered in `σ`. -/
structure Top (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rsp : s.gpr .rsp = σ.gpr .rsp
  regs : ∀ m ∈ sgM, s.gpr m.1 = σ.gpr m.2
  saved : ∀ k < 6, s.mem.readW (pa s (sc (oSV + 8 * k))) 64 = σ.gpr (savedReg k)
  ret : s.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64
  /-- The flag `r9` of entry, at `FL`. -/
  flag : s.mem.readW (pa s (sc oFL)) 64 = σ.gpr .r9

section
variable {p : Params} {D : Nat} {σ : State} (hp : (signK p D).pre σ)
include hp

/-- The layout with the first `L` bytes of the key at `rbp`. -/
theorem sgLayL {L : Nat} (hL : L ≤ skL p σ) (hD : D < 2 ^ 32)
    (hsz : scrLen p < 2 ^ 32 ∧ L < 2 ^ 32 ∧ p.sigLen < 2 ^ 32) {s : State}
    (h : Top σ s) : Lay D [(.rbp, L), (.r12, 64), (.r13, 32)] (sgW p) s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, r1, r2, r3, r4, r5, k1, k2, k3, k4, k5, n1, n2, n3, n4, n5, hsp, -⟩ := hp
  have hsub : Region.Sub ⟨σ.gpr .rdi, L⟩ ⟨σ.gpr .rdi, skL p σ⟩ := Region.sub_prefix hL
  replace d1 := d1.sub_left hsub
  replace d2 := d2.sub_left hsub
  replace r1 := r1.sub_right hsub
  replace k1 := k1.sub_right hsub
  replace n1 : (σ.gpr .rdi).toNat + L ≤ 2 ^ 64 := by omega_using [hL, n1]
  have e1 : s.gpr .rbx = σ.gpr .r8 := h.regs (.rbx, .r8) (by decide)
  have e2 : s.gpr .rbp = σ.gpr .rdi := h.regs (.rbp, .rdi) (by decide)
  have e3 : s.gpr .r12 = σ.gpr .rsi := h.regs (.r12, .rsi) (by decide)
  have e4 : s.gpr .r13 = σ.gpr .rdx := h.regs (.r13, .rdx) (by decide)
  have e5 : s.gpr .r14 = σ.gpr .rcx := h.regs (.r14, .rcx) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  have memw : ∀ r ∈ σ.wr, InRegions s.wr r.base r.len := fun r hr =>
    ⟨r, by rw [h.wr]; exact hr, Region.contains_self _ _⟩
  refine ⟨?_, fun b hb b' hb' hne hw => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    fun b hb => ?_, by rw [h.rsp]; exact hsp, hD⟩
  · intro b hb
    simp only [sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega_arith
  · simp only [sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb hb'
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl <;>
      simp only [wRegs, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, or_self, ne_eq,
        not_true_eq_false] at hne hw ⊢ <;> simp only [e1, e2, e3, e4, e5]
    all_goals first
      | exact d1 | exact d2 | exact d3 | exact d4 | exact d5 | exact d6 | exact d7
      | exact d1.symm | exact d2.symm | exact d3.symm | exact d4.symm | exact d5.symm | exact d6.symm | exact d7.symm
  · simp only [sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e1, e2, e3, e4, e5, h.rsp]
    exacts [k1, k2, k3, k5, k4]
  · simp only [sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e1, e2, e3, e4, e5]
    exacts [n1, n2, n3, n5, n4]
  · simp only [sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e1, e2, e3, e4, e5]
    exacts [⟨⟨σ.gpr .rdi, skL p σ⟩, by rw [h.rd, h.wr, hrd]; simp, contains_prefix hL⟩, mem ⟨σ.gpr .rsi, 64⟩ (by rw [hrd]; simp),
      mem ⟨σ.gpr .rdx, 32⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .r8, scrLen p⟩ (by rw [hwr]; simp),
      mem ⟨σ.gpr .rcx, p.sigLen⟩ (by rw [hwr]; simp)]
  · simp only [sgW, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp only [e1, e5]
    exacts [memw ⟨σ.gpr .r8, scrLen p⟩ (by rw [hwr]; simp), memw ⟨σ.gpr .rcx, p.sigLen⟩ (by rw [hwr]; simp)]
  · simp only [sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [retR, e1, e2, e3, e4, e5, h.rsp]
    exacts [r1, r2, r3, r5, r4]

theorem sgLay (hD : D < 2 ^ 32) (hsz : scrLen p < 2 ^ 32 ∧ p.skLen < 2 ^ 32 ∧ p.sigLen < 2 ^ 32) {s : State}
    (h : Top σ s) : Lay D (sgR p) (sgW p) s :=
  sgLayL hp (skLen_le_skL p σ) hD hsz h

end

/-- The saved registers and the return address are apart from the regions `ws`. -/
def topChk (bs : List (Reg × Nat)) (ws : List (Ptr × Nat)) : Bool :=
  (List.range 6).all (fun k => keepB bs ws (sc (oSV + 8 * k)) 8) && ws.all (fun w => inB bs w.1 w.2) &&
    keepB bs ws (sc oFL) 8

theorem Top.step {D : Nat} {σ s s' : State} {rbs wbs : List (Reg × Nat)} (h : Top σ s)
    (L : Lay D rbs wbs s) {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws)
    (hc : topChk (rbs ++ wbs) ws = true) : Top σ s' := by
  simp only [topChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  refine ⟨hP.rd.trans h.rd, hP.wr.trans h.wr, hP.rsp.trans h.rsp,
    fun m hm => (hP.bs _ (sgM_bases m hm)).trans (h.regs m hm), fun k hk => ?_, ?_,
    by rw [L.keepW hP hc.2]; exact h.flag⟩
  · rw [L.keepW hP (hc.1.1 k hk)]; exact h.saved k hk
  · have := L.keepRet hP hc.1.2
    rw [h.rsp] at this
    rw [this, h.ret]

/-! ## Saving the registers -/

theorem readW_writeW_slot (m : Mem) (a : Addr) {x y : Nat} (v : BitVec 64) (hxy : x + 8 ≤ y ∨ y + 8 ≤ x)
    (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (m.writeW (a + BitVec.ofNat 64 y) v).readW (a + BitVec.ofNat 64 x) 64 = m.readW (a + BitVec.ofNat 64 x) 64 := by
  refine Mem.readW_writeW_sep ?_ (by decide)
  rcases hxy with h | h
  · exact (off_disj (base := a) h (by omega_arith)).sep (Region.contains_self _ _) (Region.contains_self _ _)
  · exact (off_disj (base := a) h (by omega_arith)).symm.sep (Region.contains_self _ _) (Region.contains_self _ _)

/-- The six stores of `topPro`: each slot holds its register. -/
theorem stores_read (m : Mem) (a : Addr) (v : Nat → BitVec 64) : ∀ k < 6,
    ((((((m.writeW (a + BitVec.ofNat 64 840) (v 0)).writeW (a + BitVec.ofNat 64 848) (v 1)).writeW
      (a + BitVec.ofNat 64 856) (v 2)).writeW (a + BitVec.ofNat 64 864) (v 3)).writeW (a + BitVec.ofNat 64 872)
      (v 4)).writeW (a + BitVec.ofNat 64 880) (v 5)).readW (a + BitVec.ofNat 64 (oSV + 8 * k)) 64 = v k := by
  intro k hk
  rcases (by omega_arith : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (disch := omega_arith) only [oSV, Nat.reduceMul, Nat.reduceAdd, readW_writeW_slot, Mem.readW_writeW_self64]

theorem pro_eq : pro = [.store (VG.Impl.MlKem.X86_64.at_ .r8 840) .rbx, .store (VG.Impl.MlKem.X86_64.at_ .r8 848) .rbp,
    .store (VG.Impl.MlKem.X86_64.at_ .r8 856) .r12, .store (VG.Impl.MlKem.X86_64.at_ .r8 864) .r13,
    .store (VG.Impl.MlKem.X86_64.at_ .r8 872) .r14, .store (VG.Impl.MlKem.X86_64.at_ .r8 880) .r15, .mov .rbx (.reg .r8),
    .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx), .mov .r14 (.reg .rcx),
    .mov32 .r15 (.imm 1), .store (VG.Impl.MlKem.X86_64.at_ .r8 952) .r9] := rfl

theorem pro_ok {p : Params} {D : Nat} {σ : State} (hp : (signK p D).pre σ) (hsz : scrLen p < 2 ^ 32) :
    WP isa (.block pro) σ fun s => Top σ s ∧ s.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64 ∧
      Frame [⟨σ.gpr .r8, scrLen p⟩] σ.mem s.mem ∧ s.gpr .r15 = 1 := by
  have hp' := hp
  obtain ⟨_, hwr, _, _, _, _, _, _, _, _, _, _, _, r5, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hp'
  have hS : ⟨σ.gpr .r8, scrLen p⟩ ∈ σ.wr := by rw [hwr]; simp
  have c : ∀ o, o + 8 ≤ 960 → (⟨σ.gpr .r8, scrLen p⟩ : Region).Contains (σ.gpr .r8 + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' (by have : 960 ≤ scrLen p := by unfold scrLen scratchWords; omega_arith
                                     omega_arith) (by omega_arith)
  have w : ∀ o, o + 8 ≤ 960 → InRegions σ.wr (σ.gpr .r8 + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega_arith); have w1 := w 848 (by omega_arith); have w2 := w 856 (by omega_arith)
  have w3 := w 864 (by omega_arith); have w4 := w 872 (by omega_arith); have w5 := w 880 (by omega_arith)
  have w6 := w 952 (by omega_arith)
  rw [pro_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun s =>
    s.mem = ((((((σ.mem.writeW (σ.gpr .r8 + BitVec.ofNat 64 840) (σ.gpr .rbx)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 848) (σ.gpr .rbp)).writeW (σ.gpr .r8 + BitVec.ofNat 64 856) (σ.gpr .r12)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 864) (σ.gpr .r13)).writeW (σ.gpr .r8 + BitVec.ofNat 64 872) (σ.gpr .r14)).writeW
      (σ.gpr .r8 + BitVec.ofNat 64 880) (σ.gpr .r15)).writeW (σ.gpr .r8 + BitVec.ofNat 64 952) (σ.gpr .r9) ∧
    s.gpr .rbx = σ.gpr .r8 ∧ s.gpr .rbp = σ.gpr .rdi ∧ s.gpr .r12 = σ.gpr .rsi ∧ s.gpr .r13 = σ.gpr .rdx ∧
    s.gpr .r14 = σ.gpr .rcx ∧ s.gpr .r15 = 1)
    (by xrun [w0, w1, w2, w3, w4, w5, w6]) (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, h13, h14, h15⟩, k⟩ => ?_
  have hf : Frame [⟨σ.gpr .r8, scrLen p⟩] σ.mem s.mem := by
    rw [hm]
    exact ((((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega_arith))).writeW (List.mem_singleton_self _) _ (c 856 (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega_arith))).writeW (List.mem_singleton_self _) _ (c 872 (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega_arith))).writeW
      (List.mem_singleton_self _) _ (c 952 (by omega_arith)))
  have hret : s.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64 :=
    hf.readW (Region.contains_self _ _) (by simpa using r5) (by decide)
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  refine ⟨⟨k.2.1, k.2.2, hsp, fun m hm => ?_, fun j hj => ?_, hret, ?_⟩, hret, hf, h15⟩
  · simp only [sgM, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    exacts [hbx, hbp, h12, h13, h14]
  · simp only [pa, hbx, hm]
    rw [readW_writeW_slot _ _ _ (by unfold oSV; omega_arith) (by unfold oSV; omega_arith) (by omega_arith)]
    exact stores_read σ.mem (σ.gpr .r8) (fun j => σ.gpr (savedReg j)) j hj
  · simp only [pa, hbx, hm, oFL]
    exact Mem.readW_writeW_self64 _ _ _

/-! ## The return -/

theorem topEpi_eq : topEpi = [.mov32 .rax (.reg .r15), .mov .r15 (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 880)),
    .mov .r14 (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 872)), .mov .r13 (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 864)),
    .mov .r12 (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 856)), .mov .rbp (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 848)),
    .mov .rbx (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 840))] := rfl

theorem topEpi_ok {σ s : State} (h : Top σ s)
    (hin : ∀ k < 6, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8) :
    WP isa (.block topEpi) s fun s' => (s'.gpr .rax).setWidth 32 = (s.gpr .r15).setWidth 32 ∧
      gprPreserved σ s' ∧ s'.mem = s.mem := by
  have e : ∀ k < 6, s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (840 + 8 * k)) 64 = σ.gpr (savedReg k) :=
    fun k hk => h.saved k hk
  have i : ∀ k < 6, InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 (840 + 8 * k)) 8 := hin
  have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide)
  have e3 := e 3 (by decide); have e4 := e 4 (by decide); have e5 := e 5 (by decide)
  have i0 := i 0 (by decide); have i1 := i 1 (by decide); have i2 := i 2 (by decide)
  have i3 := i 3 (by decide); have i4 := i 4 (by decide); have i5 := i 5 (by decide)
  rw [show savedReg 0 = .rbx from rfl] at e0; rw [show savedReg 1 = .rbp from rfl] at e1
  rw [show savedReg 2 = .r12 from rfl] at e2; rw [show savedReg 3 = .r13 from rfl] at e3
  rw [show savedReg 4 = .r14 from rfl] at e4; rw [show savedReg 5 = .r15 from rfl] at e5
  simp only [Nat.reduceMul, Nat.reduceAdd] at e0 e1 e2 e3 e4 e5 i0 i1 i2 i3 i4 i5
  rw [topEpi_eq]
  refine WP.mono (WP.keep [.rax, .r15, .r14, .r13, .r12, .rbp, .rbx] (Q := fun s' =>
    s'.gpr .rax = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32) ∧ s'.gpr .r15 = σ.gpr .r15 ∧
    s'.gpr .r14 = σ.gpr .r14 ∧ s'.gpr .r13 = σ.gpr .r13 ∧ s'.gpr .r12 = σ.gpr .r12 ∧ s'.gpr .rbp = σ.gpr .rbp ∧
    s'.gpr .rbx = σ.gpr .rbx ∧ s'.mem = s.mem) (by xrun [i0, i1, i2, i3, i4, i5, e0, e1, e2, e3, e4, e5]) (by decide))
    fun s' ⟨⟨hax, h15, h14, h13, h12, hbp, hbx, hm⟩, k⟩ => ⟨?_, ⟨fun r hr => ?_, ?_⟩, hm⟩
  · rw [hax]; apply BitVec.eq_of_toNat_eq; simp
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hbx, hbp, by rw [k.gpr (by decide), h.rsp], h12, h13, h14, h15]
  · rw [hm]; exact h.ret

/-! ## Branches on `r15` -/

/-- A block that writes only `r15`'s flags keeps `PostB`. -/
theorem test15_ok (s : State) (D : Nat) :
    WP isa (.block [.alu32 .test .r15 (.reg .r15)]) s fun s₁ => PPostB D s s₁ [] ∧
      (∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
      s₁.zf = some ((s.gpr .r15).setWidth 32 == 0) := by
  refine WP.mono (WP.keep [.r15] (Q := fun s₁ => s₁.mem = s.mem ∧ s₁.gpr .r15 = s.gpr .r15 ∧
      s₁.zf = some (((s.gpr .r15).setWidth 32 &&& (s.gpr .r15).setWidth 32) == 0)) (by xrun) (by decide))
    fun s₁ ⟨⟨hm, h15, hz⟩, k⟩ => ⟨⟨k.2.1, k.2.2, fun r hr => k.gpr (by
        simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), k.gpr (by decide),
        by rw [hm]; exact Frame.refl _ _⟩,
      fun r hr => by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | exact h15 | exact k.gpr (by decide), hm, by rw [hz, BitVec.and_self]⟩

theorem ifOkElse_ok {D : Nat} {t e : Prog isa} {s : State} {Q : State → Prop}
    (ht : ∀ s₁, PPostB D s s₁ [] → (∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r) → s₁.mem = s.mem →
      (s.gpr .r15).setWidth 32 ≠ 0 → WP isa t s₁ Q)
    (he : ∀ s₁, PPostB D s s₁ [] → (∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r) → s₁.mem = s.mem →
      (s.gpr .r15).setWidth 32 = 0 → WP isa e s₁ Q) : WP isa (ifOkElse t e) s Q := by
  unfold ifOkElse
  refine WP.seq (WP.mono (test15_ok s D) fun s₁ ⟨hP, hcs, hm, hz⟩ => ?_)
  refine WP.ite (M := isa) (!((s.gpr .r15).setWidth 32 == 0))
    (show s₁.zf.map (!·) = _ by rw [hz]; rfl) (fun hb => ?_) fun hb => ?_
  · exact ht s₁ hP hcs hm (by simpa using hb)
  · exact he s₁ hP hcs hm (by simpa using hb)

theorem ifOkElse_tr {D : Nat} {t e : Prog isa} {P Q : State → State → Prop}
    (hq : ∀ x y, P x y → (x.gpr .r15).setWidth 32 = (y.gpr .r15).setWidth 32)
    (ht : RelCT isa (fun x y => ∃ x₀ y₀, P x₀ y₀ ∧ (PPostB D x₀ x [] ∧ (∀ r ∈ calleeSaved, x.gpr r = x₀.gpr r) ∧
      x.mem = x₀.mem) ∧ (PPostB D y₀ y [] ∧ (∀ r ∈ calleeSaved, y.gpr r = y₀.gpr r) ∧ y.mem = y₀.mem) ∧
      (x₀.gpr .r15).setWidth 32 ≠ 0) t Q)
    (he : RelCT isa (fun x y => ∃ x₀ y₀, P x₀ y₀ ∧ (PPostB D x₀ x [] ∧ (∀ r ∈ calleeSaved, x.gpr r = x₀.gpr r) ∧
      x.mem = x₀.mem) ∧ (PPostB D y₀ y [] ∧ (∀ r ∈ calleeSaved, y.gpr r = y₀.gpr r) ∧ y.mem = y₀.mem) ∧
      (x₀.gpr .r15).setWidth 32 = 0) e Q) :
    RelCT isa P (ifOkElse t e) Q := by
  unfold ifOkElse
  refine RelCT.seq (VG.Proof.MlKem.X86_64.RelCT.postDep (block_nomem_tr fun i hi s => by
      simp only [List.mem_singleton] at hi; subst hi; rfl)
    (F := fun x x₁ => (PPostB D x x₁ [] ∧ (∀ r ∈ calleeSaved, x₁.gpr r = x.gpr r) ∧ x₁.mem = x.mem) ∧
      x₁.zf = some ((x.gpr .r15).setWidth 32 == 0))
    (fun x y _ => ⟨WP.mono (test15_ok x D) fun _ h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩,
      WP.mono (test15_ok y D) fun _ h => ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩⟩)
    (Q := fun x₁ y₁ => ∃ x₀ y₀, P x₀ y₀ ∧
      ((PPostB D x₀ x₁ [] ∧ (∀ r ∈ calleeSaved, x₁.gpr r = x₀.gpr r) ∧ x₁.mem = x₀.mem) ∧
        x₁.zf = some ((x₀.gpr .r15).setWidth 32 == 0)) ∧
      ((PPostB D y₀ y₁ [] ∧ (∀ r ∈ calleeSaved, y₁.gpr r = y₀.gpr r) ∧ y₁.mem = y₀.mem) ∧
        y₁.zf = some ((y₀.gpr .r15).setWidth 32 == 0)))
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.ite ?_ ?_ ?_)
  · rintro x₁ y₁ ⟨x₀, y₀, hp, ⟨_, hx⟩, ⟨_, hy⟩⟩
    show x₁.zf.map (!·) = y₁.zf.map (!·)
    rw [hx, hy, hq x₀ y₀ hp]
  · refine RelCT.mono ht (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, hx⟩, ⟨h2, _⟩⟩, hc⟩ => ⟨x₀, y₀, hp, h1, h2, ?_⟩)
      fun _ _ h => h
    have hc' : x₁.zf.map (!·) = some true := hc
    rw [hx] at hc'
    simpa using hc'
  · refine RelCT.mono he (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, hx⟩, ⟨h2, _⟩⟩, hc⟩ => ⟨x₀, y₀, hp, h1, h2, ?_⟩)
      fun _ _ h => h
    have hc' : x₁.zf.map (!·) = some false := hc
    rw [hx] at hc'
    simpa using hc'

/-! ## Sequences -/

theorem seqR_ok {f : Nat → Prog isa} {I : Nat → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → ∀ s, I k s → WP isa (f k) s (I (k + 1))) →
      ∀ s, I a s → WP isa (seqR f a n) s (I (a + n))
  | 0, a, _, s, hs => WP.block_nil hs
  | n + 1, a, h, s, hs => by
    rw [seqR]
    refine WP.seq (WP.mono (h a (Nat.le_refl _) (by omega_arith) s hs) fun s₁ h₁ => ?_)
    rw [show a + (n + 1) = a + 1 + n by omega_arith]
    exact seqR_ok n (a + 1) (fun k hk hk' => h k (by omega_arith) (by omega_arith)) s₁ h₁

/-- `seqOk`: each piece from `I k` to `I (k + 1)`, and `I k` kept by the
test of `r15` after it; it ends in `I k` after the last piece, or after the
first that leaves `r15 = 0`. -/
theorem seqOk_ok {D : Nat} {f : Nat → Prog isa} {I : Nat → State → Prop} :
    ∀ (n a : Nat), (∀ k, a < k → k ≤ a + n → ∀ s s₁, I k s → PPostB D s s₁ [] →
        (∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r) → s₁.mem = s.mem → I k s₁) →
      (∀ k, a ≤ k → k < a + n → ∀ s, I k s → WP isa (f k) s (I (k + 1))) →
      ∀ s, I a s → WP isa (seqOk f a n) s fun s' => ∃ k, a ≤ k ∧ k ≤ a + n ∧ I k s' ∧
        (k = a + n ∨ (s'.gpr .r15).setWidth 32 = 0)
  | 0, a, _, _, s, hs => WP.block_nil ⟨a, Nat.le_refl _, by omega_using [], hs, .inl rfl⟩
  | n + 1, a, hst, h, s, hs => by
    rw [seqOk]
    refine WP.seq (WP.mono (h a (Nat.le_refl _) (by omega_using []) s hs) fun s₁ h₁ => ?_)
    refine ifOkElse_ok (D := D) (fun s₂ hP hcs hm _ => ?_) fun s₂ hP hcs hm he => ?_
    · refine WP.mono (seqOk_ok n (a + 1) (fun k hk hk' => hst k (by omega_using [hk]) (by omega_using [hk']))
        (fun k hk hk' => h k (by omega_using [hk]) (by omega_using [hk'])) s₂ (hst _ (by omega_using []) (by omega_using []) _ _ h₁ hP hcs hm))
        fun s' ⟨k, hk, hk', hI, hk''⟩ => ⟨k, by omega_using [hk], by omega_using [hk'], hI, hk''.imp (fun _ => by omega_arith) id⟩
    · exact WP.block_nil ⟨a + 1, by omega_using [], by omega_using [], hst _ (by omega_using []) (by omega_using []) _ _ h₁ hP hcs hm,
        .inr (by rw [hcs _ (by decide)]; exact he)⟩

theorem seqR_tr {f : Nat → Prog isa} {R : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → RelCT isa (R k) (f k) (R (k + 1))) →
      RelCT isa (R a) (seqR f a n) (R (a + n))
  | 0, _, _ => nil_tr
  | n + 1, a, h => by
    rw [seqR, show a + (n + 1) = a + 1 + n by omega_arith]
    exact RelCT.seq (h a (Nat.le_refl _) (by omega_arith)) (seqR_tr n (a + 1) fun k hk hk' => h k (by omega_arith) (by omega_arith))

end VG.Proof.MlDsa.X86_64.Sign
