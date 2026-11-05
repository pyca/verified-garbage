module
-- separate module: its proofs (the candidate loop, about 2 s) build in parallel with `Core`'s, which `Loop` also imports

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Prep
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Steps
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy

/-!
# Deterministic ECDSA on x86-64: the candidate

The candidate `T`, at `fT` above the frame's pointers, its length at `fTlen`:
empty (`tInit_ok`), then, while it is shorter than `Q` bytes, `V = HMAC_K(V)`
appended to it (`step_ok`: `hmacVR_ok`, `keepArgs_ok`, `cp_ok`, `tStep_ok`),
which the loop does `nV P = ⌈Q / D⌉` times, RFC 6979's number of blocks
(`nV_eq`): `T` is then `genT`'s (`loop_ok`), and `k`, its first `Q` bytes,
shifted right by `sh` bits if `big` (`candTop_ok`), is `bits2int` of it
(`cand_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

/-- `T`'s length. -/
abbrev tlen {dn : Nat} (L : Lay dn) (m : Mem) : BitVec 64 := m.readW (L.B + BitVec.ofNat 64 (24 + fTlen)) 64

/-- `T`'s first `n` bytes. -/
abbrev tOf {dn : Nat} (L : Lay dn) (m : Mem) (n : Nat) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 (24 + fT)) n

/-! ## The blocks -/

/-- `T` empty. -/
theorem tInit_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.tInit) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 (24 + fTlen), 8⟩] t.mem t'.mem ∧ tlen L t'.mem = BitVec.ofNat 64 0 := by
  have w := hc.inFrW (d := 152) (n := 8) (by omega_arith) (by have := L.he; omega_arith)
  refine Ctx.of_keep hL hc ?_ (by rfl) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by decide)
  apply WP.of_runBlock
  simp only [Cfg.tInit, fTlen, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32,
    State.setReg32, State.store64, ea_stk, RegUpd.gpr_setReg_self, RegUpd.gpr_arithFlags, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags,
    RegUpd.gpr_setReg, reduceCtorEq, ite_false, hc.rsp, Offset.add_add, Nat.reduceAdd, w, ite_true,
    Option.bind_some, xor_self_zx, Option.some.injEq, exists_eq_left']
  exact ⟨by triv, by triv, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _),
    Mem.readW_writeW_self64 _ _ _⟩

/-- `r8 = 0`. -/
theorem r8z_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (.block [.alu32 .xor .r8 (.reg .r8)]) u (Upd L g m₀ u .r8 (BitVec.ofNat 64 0)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, State.setReg32,
    Option.bind_some, xor_self_zx, Option.some.injEq, exists_eq_left']
  refine ⟨hc.set hL (d := .r8) (by decide) rfl rfl rfl rfl fun r hr => ?_, rfl, RegUpd.gpr_setReg_self _ _ _,
    fun r hr => ?_⟩
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]
  · rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- The arguments of `V`'s copy to the end of `T`, of `a` bytes: `V` in
`rsi`, `T + a` in `rdi`, `rcx = D` and `r8 = 0`. -/
theorem keepArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {a : Nat}
    (ha : tlen L t.mem = BitVec.ofNat 64 a) :
    WP isa (.block Cfg.keepArgs) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧
      u.gpr .rsi = L.B + BitVec.ofNat 64 (24 + fV) ∧ u.gpr .rdi = L.B + BitVec.ofNat 64 (24 + fT + a) ∧
      u.gpr .rcx = BitVec.ofNat 64 P.H.D ∧ u.gpr .r8 = BitVec.ofNat 64 0 := by
  have he := L.he
  rw [Cfg.keepArgs, show ([.alu .add .rdi (.mem (stk fTlen)), .mov .rcx (.mem (stk fDl)),
      .alu32 .xor .r8 (.reg .r8)] : List Instr) =
    [.alu .add .rdi (.mem (stk fTlen))] ++ [.mov .rcx (.mem (stk fDl))] ++ [.alu32 .xor .r8 (.reg .r8)] from rfl,
    WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .rsi) (by decide) (o := fV) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (fr_ok hL h₁.ctx (d := .rdi) (by decide) (o := fT) (by decide)) fun u₂ h₂ => ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (addF_ok hL h₂.ctx (d := .rdi) (by decide) (o := fTlen) (by simp only [fTlen]; omega))
    fun u₃ h₃ => ?_
  refine WP.mono (ldF_ok hL h₃.ctx (d := .rcx) (by decide) (o := fDl) (by simp only [fDl]; omega)) fun u₄ h₄ => ?_
  refine WP.mono (r8z_ok hL h₄.ctx) fun u₅ h₅ => ?_
  have hm₄ : u₄.mem = t.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨h₅.ctx, by rw [h₅.mem, hm₄], ?_, ?_, ?_, h₅.val⟩
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₅.keep _ (by decide), h₄.keep _ (by decide), h₃.val, h₂.val, h₂.mem, h₁.mem,
      show t.mem.readW (L.B + BitVec.ofNat 64 (24 + fTlen)) 64 = tlen L t.mem from rfl, ha, Offset.add_add]
  · rw [h₅.keep _ (by decide), h₄.val, h₃.mem, h₂.mem, h₁.mem, hc.dl hT]

/-- `T`'s length `n` stored, and the carry flag set iff `n < Q`. -/
theorem stCmp_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {n : Nat} (hax : u.gpr .rax = BitVec.ofNat 64 n)
    (hn : n < 2 ^ 63) :
    WP isa (.block [.store (stk fTlen) .rax, .alu .cmp .rax (.imm (BitVec.ofNat 32 P.Q))]) u fun u' =>
      Ctx L g m₀ u' ∧ Frame [⟨L.B + BitVec.ofNat 64 (24 + fTlen), 8⟩] u.mem u'.mem ∧
      tlen L u'.mem = BitVec.ofNat 64 n ∧ u'.cf = some (decide (n < P.Q)) := by
  have w := hc.inFrW (d := 152) (n := 8) (by omega_arith) (by have := L.he; omega_arith)
  have hQ : P.Q < 2 ^ 31 := by nums
  have hQt : (BitVec.ofNat 64 P.Q).toNat = P.Q := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnt : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine Ctx.of_keep hL hc ?_ (by rfl) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by decide)
  apply WP.of_runBlock
  simp only [fTlen, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, sx32 hQ,
    State.store64, ea_stk, hc.rsp, Offset.add_add, Nat.reduceAdd, w, ite_true, hax, hQt, hnt,
    RegUpd.wr_arithFlags, RegUpd.rd_arithFlags, RegUpd.mem_arithFlags, RegUpd.cf_arithFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨by triv, by triv, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _),
    Mem.readW_writeW_self64 _ _ _, trivial⟩

/-- `T` longer by `D` bytes, and the carry flag set iff it is still shorter than `Q`. -/
theorem tStep_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) {a : Nat}
    (ha : tlen L u.mem = BitVec.ofNat 64 a) (hn : a + P.H.D < 2 ^ 63) :
    WP isa (.block (cfgOf P).tStep) u fun u' => Ctx L g m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 (24 + fTlen), 8⟩] u.mem u'.mem ∧
      tlen L u'.mem = BitVec.ofNat 64 (a + P.H.D) ∧ u'.cf = some (decide (a + P.H.D < P.Q)) := by
  have he := L.he
  rw [show (cfgOf P).tStep = [.mov .rax (.mem (stk fTlen))] ++ [.alu .add .rax (.mem (stk fDl))] ++
      [.store (stk fTlen) .rax, .alu .cmp .rax (.imm (BitVec.ofNat 32 P.Q))] from rfl,
    WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldF_ok hL hc (d := .rax) (by decide) (o := fTlen) (by simp only [fTlen]; omega)) fun u₁ h₁ => ?_
  refine WP.mono (addF_ok hL h₁.ctx (d := .rax) (by decide) (o := fDl) (by simp only [fDl]; omega)) fun u₂ h₂ => ?_
  have hax : u₂.gpr .rax = BitVec.ofNat 64 (a + P.H.D) := by
    rw [h₂.val, h₁.val, h₁.mem, hc.dl hT, show u.mem.readW (L.B + BitVec.ofNat 64 (24 + fTlen)) 64 = tlen L u.mem
      from rfl, ha, BitVec.ofNat_add_ofNat]
  refine WP.mono (stCmp_ok hL h₂.ctx hax hn) fun u₃ ⟨hc₃, hf₃, hl₃, hcf₃⟩ => ?_
  rw [h₂.mem, h₁.mem] at hf₃
  exact ⟨hc₃, hf₃, hl₃, hcf₃⟩

/-! ## The loop -/

/-- What the candidate's loop changes: `scratch`, the stack below the
frame, `K`, `V` and `T`'s length, and `T`. -/
abbrev CW {dn : Nat} (L : Lay dn) : List Region :=
  [L.SCR, ⟨L.B, 160⟩, ⟨L.B + BitVec.ofNat 64 (24 + fT), 136⟩]

/-- After `j` of the candidate's `V`s, from `V₀` with the key `K`. -/
structure CI (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 64) (m₀ : Mem) (t₀ : State)
    (K V₀ : List Byte) (j : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame (CW L) t₀.mem u.mem
  k : kOf P L u.mem = K
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K j V₀).2
  len : tlen L u.mem = BitVec.ofNat 64 (j * P.H.D)
  t : tOf L u.mem (j * P.H.D) = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H K j V₀).1
  saved : SavedK P L u.mem K

/-- One more `V`. -/
theorem step_ok (hL : L.Ok) (hT : TabL P L) {t₀ : State} {K V₀ : List Byte} {j : Nat} (hj : (j + 1) * P.H.D ≤ 136)
    {u : State} (hI : CI P L g m₀ t₀ K V₀ j u) :
    WP isa (cfgOf P).candStep u fun u' => CI P L g m₀ t₀ K V₀ (j + 1) u' ∧
      u'.cf = some (decide ((j + 1) * P.H.D < P.Q)) := by
  have he := L.he
  have hnb := hL.nb
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  have hjD : (j + 1) * P.H.D = j * P.H.D + P.H.D := Nat.succ_mul _ _
  have hS : SavedK P L u.mem (kOf P L u.mem) := by rw [hI.k]; exact hI.saved
  refine WP.seq (WP.mono (hmacVR_ok hL hT hI.ctx hS) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁, hS₁⟩ => ?_)
  have hl₁ : tlen L u₁.mem = BitVec.ofNat 64 (j * P.H.D) := by
    rw [← hI.len]
    exact hf₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by simp only [fTlen]; omega)
      · exact Offset.disjoint_base _ (by simp only [fTlen]; omega) (by simp only [fTlen]; omega)) (by decide)
  have ht₁ : Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (24 + fT)) (j * P.H.D) =
      Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + fT)) (j * P.H.D) :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by simp only [fT]; omega)
      · exact Offset.disjoint_base _ (by simp only [fT]; omega) (by simp only [fT]; omega)) (by omega)
  refine WP.seq (WP.mono (keepArgs_ok hL hT hc₁ hl₁) fun u₂ ⟨hc₂, hm₂, hsi₂, hdi₂, hcx₂, h8₂⟩ => ?_)
  refine WP.seq (WP.mono (cp_ok hL hc₂ (p := L.B + BitVec.ofNat 64 (24 + fT + j * P.H.D))
      (q := L.B + BitVec.ofNat 64 (24 + fV)) (n := P.H.D) (by omega) (by omega) hcx₂ hdi₂ hsi₂ h8₂ ?_
      (hc₂.inFrW (by omega) (by simp only [fT]; omega))
      (safe_high L (by simp only [fT]; omega) (by simp only [fT]; omega))
      (fun i hi => by
        obtain ⟨R, hR, h⟩ := hc₂.inFrW (d := 24 + fV + i) (n := 1) (by omega) (by simp only [fV]; omega)
        exact ⟨R, List.mem_append_right _ hR, by rw [Offset.add_add]; exact h⟩)
      (fun i hi h => Offset.disjoint L.B (d := 24 + fV + i) (n := 1) (e := 24 + fT + j * P.H.D) (k := P.H.D)
        (.inl (by simp only [fV, fT]; omega)) (by simp only [fV]; omega) (by simp only [fT]; omega) _
        (by rw [← Offset.add_add]; exact Region.contains_self _ _) h))
    fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ?_)
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 24 + fT + _) (by simp only [fT]; omega),
      Nat.mod_eq_of_lt (by simp only [fT]; omega)]
    simp only [fT]; omega
  rw [hm₂] at hf₃ hb₃
  have hl₃ : tlen L u₃.mem = BitVec.ofNat 64 (j * P.H.D) := by
    rw [← hl₁]
    exact hf₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by simp only [fTlen, fT]; omega)) (by simp only [fTlen]; omega)
        (by simp only [fT]; omega)) (by decide)
  refine WP.mono (tStep_ok hL hT hc₃ hl₃ (by omega)) fun u₄ ⟨hc₄, hf₄, hl₄, hcf₄⟩ => ?_
  -- What the copy and the length's store keep.
  have kp : ∀ {o n : Nat}, 24 ≤ o → o + n ≤ 24 + fTlen →
      Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 o) n = Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 o) n :=
    fun h₁ h₂ => by
      rw [bytesAt_frame hf₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl h₂) (by simp only [fTlen] at h₂ ⊢; omega) (by simp only [fTlen]; omega))
        (by simp only [fTlen] at h₂; omega),
        bytesAt_frame hf₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by simp only [fTlen, fT] at h₂ ⊢; omega)) (by simp only [fTlen] at h₂ ⊢; omega)
            (by simp only [fT]; omega)) (by simp only [fTlen] at h₂; omega)]
  have hK : kOf P L u₄.mem = K := by
    rw [show kOf P L u₄.mem = Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 24) P.H.D from rfl,
      kp (by decide) (by simp only [fTlen]; omega)]
    exact hk₁.trans hI.k
  refine ⟨⟨hc₄, ?_, hK, ?_, ?_, ?_, ?_⟩, by rw [hcf₄, hjD]⟩
  · refine ((hI.frame.trans (hf₁.sub fun r hr => ?_)).trans (hf₃.sub fun r hr => ?_)).trans (hf₄.sub fun r hr => ?_)
    · simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨⟨L.B, 160⟩, by simp, Region.sub_prefix (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B + BitVec.ofNat 64 (24 + fT), 136⟩, by simp, Offset.sub _ (by omega) (by omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨L.B, 160⟩, by simp, Offset.sub_base _ (by simp only [fTlen]; omega)⟩
  · rw [show vOf P L u₄.mem = Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 88) P.H.D from rfl,
      kp (by decide) (by simp only [fTlen]; omega), genT_succ]
    show vOf P L u₁.mem = _
    rw [hv₁, hI.k, hI.v]
  · rw [hl₄, hjD]
  · show Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 (24 + fT)) ((j + 1) * P.H.D) = _
    rw [hjD, Proof.Hmac.Common.bytesAt_add, Offset.add_add,
      bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by simp only [fTlen, fT]; omega)) (by simp only [fT]; omega)
          (by simp only [fTlen]; omega)) (by omega),
      bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by simp only [fTlen, fT]; omega)) (by simp only [fT]; omega)
          (by simp only [fTlen]; omega)) (by omega),
      hb₃, bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by omega)) (by simp only [fT]; omega) (by simp only [fT]; omega)) (by omega),
      ht₁, show Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (24 + fT)) (j * P.H.D) = _ from hI.t, genT_succ]
    rw [show Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (24 + fV)) P.H.D = vOf P L u₁.mem from rfl, hv₁, hI.k,
      hI.v]
  · rw [hk₁, hI.k] at hS₁
    refine (hS₁.frame hf₃ fun r hr => ?_).frame hf₄ fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_scr (by simp only [fT]; omega) (by decide)).symm
    · simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_scr (by simp only [fTlen]; omega) (by decide)).symm

/-- The number of `V`s in a candidate: `⌈Q / D⌉`. -/
abbrev RfcHash.nV (P : RfcHash) : Nat := (P.Q + P.H.D - 1) / P.H.D

theorem nV_lt (P : RfcHash) (j : Nat) : j + 1 < P.nV ↔ (j + 1) * P.H.D < P.Q := by
  obtain ⟨-, -, -, -, -, -, hD16, -, -, -, -, -, -, -, hQ8, -, -, -⟩ := P.sizes
  rw [RfcHash.nV, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega), Nat.succ_mul (j + 1)]
  omega

theorem nV_facts (P : RfcHash) : 1 ≤ P.nV ∧ P.nV * P.H.D ≤ P.Q + P.H.D - 1 ∧ P.Q ≤ P.nV * P.H.D := by
  obtain ⟨-, -, -, -, -, -, hD16, -, -, -, -, -, -, -, hQ8, -, -, -⟩ := P.sizes
  have e₁ := Nat.div_mul_le_self (P.Q + P.H.D - 1) P.H.D
  have e₂ := Nat.lt_mul_div_succ (P.Q + P.H.D - 1) (show 0 < P.H.D by omega)
  have e₃ : 1 ≤ P.nV := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  simp only [RfcHash.nV] at e₃ ⊢
  generalize (P.Q + P.H.D - 1) / P.H.D = N at e₁ e₂ e₃ ⊢
  rw [Nat.mul_succ, Nat.mul_comm] at e₂
  omega

/-- RFC 6979's number of blocks is `⌈Q / D⌉`. -/
theorem nV_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.H.D = P.nV := by
  obtain ⟨-, -, -, -, -, -, hD16, -, -, -, -, -, -, -, hQ8, -, -, -⟩ := P.sizes
  have hl := P.R.nBits_len
  have e₁ := Nat.div_mul_le_self (P.Q + P.H.D - 1) P.H.D
  have e₂ := Nat.lt_mul_div_succ (P.Q + P.H.D - 1) (show 0 < P.H.D by omega)
  rw [Spec.Ecdsa.Rfc6979.blocks]
  simp only [RfcHash.nV, RfcHash.Q] at e₁ e₂ hQ8 ⊢
  generalize (P.R.E.C.len + P.H.D - 1) / P.H.D = N at e₁ e₂ ⊢
  rw [Nat.mul_succ, Nat.mul_comm] at e₂
  have h₁ : N * (8 * P.H.D) = 8 * (N * P.H.D) := Nat.mul_left_comm _ _ _
  have h₂ : (N + 1) * (8 * P.H.D) = 8 * (N * P.H.D) + 8 * P.H.D := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_left_comm]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- The loop: `nV` `V`s. -/
theorem loop_ok (hL : L.Ok) (hT : TabL P L) {t₀ : State} {K V₀ : List Byte} {u : State}
    (hI : CI P L g m₀ t₀ K V₀ 0 u) :
    WP isa (.loop (cfgOf P).candStep .b) u (CI P L g m₀ t₀ K V₀ P.nV) := by
  obtain ⟨hN1, hND, -⟩ := nV_facts P
  obtain ⟨-, -, -, -, -, -, -, hD64, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  refine WP.loop (M := isa) (fun (n : Nat) (s : State) => ∃ j, n = P.nV - j ∧ j < P.nV ∧ CI P L g m₀ t₀ K V₀ j s)
    ?_ (P.nV - 0) u ⟨0, rfl, hN1, hI⟩
  rintro n s ⟨j, rfl, hj, hIj⟩
  have hb : (j + 1) * P.H.D ≤ 136 :=
    Nat.le_trans (Nat.mul_le_mul (show j + 1 ≤ P.nV by omega) (Nat.le_refl P.H.D)) (by omega)
  refine WP.mono (step_ok hL hT hb hIj) fun s' ⟨hI', hcf⟩ => ?_
  by_cases hlt : j + 1 < P.nV
  · exact .inr ⟨by show s'.cf = some true; rw [hcf, decide_eq_true ((nV_lt P j).mp hlt)],
      P.nV - (j + 1), by omega, j + 1, rfl, hlt, hI'⟩
  · refine .inl ⟨by show s'.cf = some false; rw [hcf, decide_eq_false (fun h => hlt ((nV_lt P j).mpr h))], ?_⟩
    rw [show P.nV = j + 1 by omega]; exact hI'

/-! ## The candidate -/

/-- `T` empty: no `V`s yet. -/
theorem tInit_ci (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (.block Cfg.tInit) t (CI P L g m₀ t (kOf P L t.mem) (vOf P L t.mem) 0) := by
  have he := L.he
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  refine WP.mono (tInit_ok hL hc) fun u₀ ⟨hc₀, hf₀, hl₀⟩ => ?_
  have kv0 : ∀ {o : Nat}, 24 ≤ o → o + P.H.D ≤ 152 →
      Spec.Sha256.bytesAt u₀.mem (L.B + BitVec.ofNat 64 o) P.H.D =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 o) P.H.D := fun h₁ h₂ =>
    bytesAt_frame hf₀ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by simp only [fTlen]; omega)) (by omega) (by simp only [fTlen]; omega))
      (by omega)
  exact
    { ctx := hc₀
      frame := hf₀.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨L.B, 160⟩, by simp, Offset.sub_base _ (by decide)⟩
      k := kv0 (by decide) (by omega)
      v := kv0 (by decide) (by omega)
      len := by rw [hl₀, Nat.zero_mul]
      t := by simp [Spec.Sha256.bytesAt, Spec.Ecdsa.Rfc6979.genT]
      saved := hS.frame hf₀ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hL.stk_scr (by simp only [fTlen]; omega) (by decide)).symm }


theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (Spec.Sha256.bytesAt m p n).length = n := by
  simp [Spec.Sha256.bytesAt]

/-- The candidate: `nV` successive `V = HMAC_K(V)`, and `k`, whose number is
`bits2int` of their concatenation, where `core` reads it. -/
theorem cand_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t)
    (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ Frame (CW L) t.mem u.mem ∧ kOf P L u.mem = kOf P L t.mem ∧
      vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).2 ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kArg P L) P.Q) =
        Spec.Ecdsa.Rfc6979.bits2int P.R.E.C
          (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 ∧
      SavedK P L u.mem (kOf P L t.mem) := by
  have he := L.he
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  have hl := P.R.nBits_len
  obtain ⟨-, hND, hQN⟩ := nV_facts P
  rw [Cfg.cand]
  refine WP.seq (WP.mono (tInit_ci hL hc hS) fun u₀ hI0 => ?_)
  refine WP.seq (WP.mono (loop_ok hL hT hI0) fun u₁ hI₁ => ?_)
  have hTl := genT_length P (kOf P L t.mem) P.nV (vOf P L t.mem)
  have hbits : Spec.Ecdsa.Rfc6979.bits2int P.R.E.C
      (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 =
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u₁.mem (kArg P L) P.Q) >>> P.R.sh := by
    rw [Spec.Ecdsa.Rfc6979.bits2int, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega)
      (by rw [hTl]; exact hQN),
      show (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 =
        Spec.Sha256.bytesAt u₁.mem (kArg P L) (P.nV * P.H.D) from hI₁.t.symm,
      ← bytesAt_take _ _ hQN, show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = P.R.sh by rw [hl.2.2]]
  cases hb : P.R.big
  · have hsh : P.R.sh = 0 := by have := (P.R.sizesA hb).2.2.1; omega
    rw [show (cfgOf P).candTop = [] by simp only [Cfg.candTop, show (cfgOf P).big = false from hb,
      Bool.false_eq_true, ite_false], WP.block_nil_iff]
    exact ⟨hI₁.ctx, hI₁.frame, hI₁.k, hI₁.v, by rw [hbits, hsh, Nat.shiftRight_zero], hI₁.saved⟩
  · have hsh8 : P.R.sh < 8 := by omega
    have hsh0 : P.R.sh ≠ 0 := by have := (P.R.sizesW hb); omega
    refine WP.mono (candTop_ok hL hb hsh0 hsh8 hI₁.ctx) fun u ⟨hcu, hf, hbu⟩ => ?_
    have kv : ∀ {o : Nat}, 24 ≤ o → o + P.H.D ≤ 152 →
        Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 o) P.H.D =
          Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 o) P.H.D := fun h₁ h₂ =>
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr (by omega) (by decide)
        · exact Offset.disjoint _ (.inl (by simp only [fT]; omega)) (by omega) (by simp only [fT]; omega)) (by omega)
    refine ⟨hcu, hI₁.frame.trans (hf.sub fun r hr => ?_), (kv (by decide) (by omega)).trans hI₁.k,
      (kv (by decide) (by omega)).trans hI₁.v, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨⟨L.B + BitVec.ofNat 64 (24 + fT), 136⟩, by simp, Region.sub_prefix (by omega)⟩
    · rw [show kArg P L = L.B + BitVec.ofNat 64 (24 + fT) from rfl, hbu, hbits,
        ofBytes_toBytes _ _ (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by
          have := ofBytes_lt (Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (24 + fT)) P.Q)
          rwa [length_bytesAt] at this))]
    · refine hI₁.saved.frame hf fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
      · exact (hL.stk_scr (by simp only [fT]; omega) (by decide)).symm

end VG.Proof.Ecdsa.Rfc6979.X86_64
