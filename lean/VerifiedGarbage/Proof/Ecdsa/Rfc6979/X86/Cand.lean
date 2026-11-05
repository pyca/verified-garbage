module
-- separate module: its proofs (the candidate loop) build in parallel with `Core`'s, which `Loop` also imports

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Prep
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Steps
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Copy
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Deterministic ECDSA on x86 (32-bit): the candidate

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Cand.lean`): the candidate `T`, at
`fT` in the frame, its length at `fTlen`: empty (`tInit_ok`), then, while it
is shorter than `Q` bytes, `V = HMAC_K(V)` appended to it (`step_ok`:
`hmacVR_ok`, `keepArgs_ok`, `cpLoop_ok`, `tStep_ok`), which the loop does
`nV P = ⌈Q / D⌉` times, RFC 6979's number of blocks (`nV_eq`): `T` is then
`genT`'s (`loop_ok`), and `k`, its first `Q` bytes, shifted right by `sh`
bits if `big` (`candTop_ok`), is `bits2int` of it (`cand_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- `T`'s length. -/
abbrev tlen {dn : Nat} (L : Lay dn) (m : Mem) : BitVec 32 := m.readW (L.B + BitVec.ofNat 64 (76 + fTlen)) 32

/-- Where `T` is. -/
abbrev kAddr {dn : Nat} (L : Lay dn) : Addr := L.B + BitVec.ofNat 64 (76 + fT)

/-- `T`'s first `n` bytes. -/
abbrev tOf {dn : Nat} (L : Lay dn) (m : Mem) (n : Nat) : List Byte := Spec.Sha256.bytesAt m (kAddr L) n

/-! ## The blocks -/

theorem tlen_addr (hL : L.Ok) : addr L.F fTlen = L.B + BitVec.ofNat 64 (76 + fTlen) := hL.addrF (by decide)

/-- `T` empty. -/
theorem tInit_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.tInit) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 (76 + fTlen), 4⟩] t.mem t'.mem ∧ tlen L t'.mem = 0 := by
  simp only [Cfg.tInit, stk]
  refine wp_movi fun u₁ v₁ => wp_stm (B := L.F) (by rw [v₁.other _ (by decide), hc.esp])
    (by rw [tlen_addr hL, v₁.wr]; exact hc.inFrW (by decide) (by decide) hL) fun u₂ v₂ => WP.block_nil ?_
  rw [tlen_addr hL, v₁.gpr, v₁.mem] at v₂
  have hf : Frame [⟨L.B + BitVec.ofNat 64 (76 + fTlen), 4⟩] t.mem u₂.mem := by
    rw [v₂.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc.keep (hsy := by rw [v₂.syms, v₁.syms]) hL (by rw [v₂.rd, v₁.rd]) (by rw [v₂.wr, v₁.wr])
    (by rw [v₂.gpr, v₁.other _ (by decide)]) hf
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by decide) (by decide)), hf, ?_⟩
  simp only [tlen, v₂.mem, Mem.readW_writeW_self32]

/-- The arguments of `V`'s copy to the end of `T`, of `a` bytes: `V` in
`esi`, `T + a` in `ebx`, `ecx = D`. -/
theorem keepArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t) {a : Nat}
    (ha : tlen L t.mem = BitVec.ofNat 32 a) :
    WP isa (.block Cfg.keepArgs) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧
      u.gpr .esi = L.F + BitVec.ofNat 32 fV ∧ u.gpr .ebx = L.F + BitVec.ofNat 32 (fT + a) ∧
      u.gpr .ecx = BitVec.ofNat 32 P.F.H.D := by
  rw [Cfg.keepArgs, show ([.alu .add .ebx (.mem (stk fTlen)), .mov .ecx (.mem (stk fDl))] : List Instr) =
    [.alu .add .ebx (.mem (stk fTlen))] ++ [.mov .ecx (.mem (stk fDl))] from rfl,
    WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .esi) (by decide) fV) fun u₁ h₁ => ?_
  refine WP.mono (fr_ok hL h₁.ctx (d := .ebx) (by decide) fT) fun u₂ h₂ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addF_ok hL h₂.ctx (d := .ebx) (by decide) (o := fTlen) (by decide)) fun u₃ h₃ => ?_
  refine WP.mono (ldF_ok hL h₃.ctx (d := .ecx) (by decide) (o := fDl) (by decide)) fun u₄ h₄ => ?_
  refine ⟨h₄.ctx, by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem], ?_, ?_, ?_⟩
  · rw [h₄.keep _ (by decide), h₃.keep _ (by decide), h₂.keep _ (by decide), h₁.val]
  · rw [h₄.keep _ (by decide), h₃.val, h₂.val, h₂.mem, h₁.mem,
      show t.mem.readW (L.B + BitVec.ofNat 64 (76 + fTlen)) 32 = tlen L t.mem from rfl, ha, BitVec.add_assoc,
      BitVec.ofNat_add_ofNat]
  · rw [h₄.val, h₃.mem, h₂.mem, h₁.mem, hc.dl hT]

/-- `T` longer by `D` bytes, and the carry flag set iff it is still shorter than `Q`. -/
theorem tStep_ok (hL : L.Ok) (hT : TabL P L) {u : State} (hc : Ctx L g m₀ u) {a : Nat}
    (ha : tlen L u.mem = BitVec.ofNat 32 a) (hn : a + P.F.H.D < 2 ^ 32) :
    WP isa (.block (cfgOf P).tStep) u fun u' => Ctx L g m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 (76 + fTlen), 4⟩] u.mem u'.mem ∧
      tlen L u'.mem = BitVec.ofNat 32 (a + P.F.H.D) ∧ u'.cf = some (decide (a + P.F.H.D < P.Q)) := by
  have hQ : P.Q < 2 ^ 32 := by nums
  rw [show (cfgOf P).tStep = [.mov .eax (.mem (stk fTlen))] ++ [.alu .add .eax (.mem (stk fDl))] ++
      [.store (stk fTlen) .eax, .alu .cmp .eax (.imm (BitVec.ofNat 32 P.Q))] from rfl,
    WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ldF_ok hL hc (d := .eax) (by decide) (o := fTlen) (by decide)) fun u₁ h₁ => ?_
  refine WP.mono (addF_ok hL h₁.ctx (d := .eax) (by decide) (o := fDl) (by decide)) fun u₂ h₂ => ?_
  have hax : u₂.gpr .eax = BitVec.ofNat 32 (a + P.F.H.D) := by
    rw [h₂.val, h₁.val, h₁.mem, hc.dl hT, show u.mem.readW (L.B + BitVec.ofNat 64 (76 + fTlen)) 32 = tlen L u.mem
      from rfl, ha, BitVec.ofNat_add_ofNat]
  have hc₂ := h₂.ctx
  refine wp_stm (B := L.F) hc₂.esp (by rw [tlen_addr hL]; exact hc₂.inFrW (by decide) (by decide) hL)
    fun u₃ v₃ => wp_cmpi fun u₄ v₄ cf₄ _ => WP.block_nil ?_
  rw [tlen_addr hL, hax] at v₃
  have hm : u₄.mem = u₂.mem.writeW (L.B + BitVec.ofNat 64 (76 + fTlen)) (BitVec.ofNat 32 (a + P.F.H.D)) := by
    rw [v₄.mem, v₃.mem]
  have hf : Frame [⟨L.B + BitVec.ofNat 64 (76 + fTlen), 4⟩] u₂.mem u₄.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hc₂.keep (hsy := by rw [v₄.syms, v₃.syms]) hL (by rw [v₄.rd, v₃.rd]) (by rw [v₄.wr, v₃.wr])
      (by rw [v₄.gpr, v₃.gpr]) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by decide) (by decide)),
    by rw [h₂.mem, h₁.mem] at hf; exact hf, by rw [tlen, hm, Mem.readW_writeW_self32], ?_⟩
  rw [cf₄, v₃.gpr, hax, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hQ]

/-! ## The loop -/

/-- What the candidate's loop changes: `scratch`, the stack below the
saved registers, `T`'s length, and `T`. -/
abbrev CW {dn : Nat} (L : Lay dn) : List Region :=
  [L.SCR, ⟨L.B, 204⟩, ⟨L.B + BitVec.ofNat 64 (76 + fTlen), 4⟩, ⟨kAddr L, 136⟩]

/-- After `j` of the candidate's `V`s, from `V₀` with the key `K`. -/
structure CI (P : RfcHash) {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (t₀ : State)
    (K V₀ : List Byte) (j : Nat) (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame (CW L) t₀.mem u.mem
  k : kOf P L u.mem = K
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H K j V₀).2
  len : tlen L u.mem = BitVec.ofNat 32 (j * P.F.H.D)
  t : tOf L u.mem (j * P.F.H.D) = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H K j V₀).1
  saved : SavedK P L u.mem K

/-- One more `V`. -/
theorem step_ok (hL : L.Ok) (hT : TabL P L) {t₀ : State} {K V₀ : List Byte} {j : Nat} (hj : (j + 1) * P.F.H.D ≤ 136)
    {u : State} (hI : CI P L g m₀ t₀ K V₀ j u) :
    WP isa (cfgOf P).candStep u fun u' => CI P L g m₀ t₀ K V₀ (j + 1) u' ∧
      u'.cf = some (decide ((j + 1) * P.F.H.D < P.Q)) := by
  have hnb := hL.nB
  obtain ⟨-, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  have hjD : (j + 1) * P.F.H.D = j * P.F.H.D + P.F.H.D := Nat.succ_mul _ _
  have hfV : fV = 64 := rfl
  have hfT : fT = 376 := rfl
  have hfTl : fTlen = 152 := rfl
  have hS : SavedK P L u.mem (kOf P L u.mem) := by rw [hI.k]; exact hI.saved
  refine WP.seq (WP.mono (hmacVR_ok hL hT hI.ctx hS) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁, hS₁⟩ => ?_)
  have hl₁ : tlen L u₁.mem = BitVec.ofNat 32 (j * P.F.H.D) := by
    rw [← hI.len]
    exact hf₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by omega)
      · exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)
  have ht₁ : Spec.Sha256.bytesAt u₁.mem (kAddr L) (j * P.F.H.D) = Spec.Sha256.bytesAt u.mem (kAddr L) (j * P.F.H.D) :=
    bytesAt_frame hf₁ (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by omega)
      · exact Offset.disjoint_base _ (by omega) (by omega)) (by omega)
  refine WP.seq (WP.mono (keepArgs_ok hL hT hc₁ hl₁) fun u₂ ⟨hc₂, hm₂, hsi₂, hbx₂, hcx₂⟩ => ?_)
  have eS : (L.F + BitVec.ofNat 32 fV).setWidth 64 = L.B + BitVec.ofNat 64 (76 + fV) := hL.frv (by decide)
  have eD : (L.F + BitVec.ofNat 32 (fT + j * P.F.H.D)).setWidth 64 = kAddr L + BitVec.ofNat 64 (j * P.F.H.D) := by
    rw [hL.frv (by omega), Offset.add_add, Nat.add_assoc]
  have hnB := hL.nB
  have hr₂ : InRegions (u₂.rd ++ u₂.wr) ((L.F + BitVec.ofNat 32 fV).setWidth 64) P.F.H.D := by
    rw [eS]
    exact ⟨L.FR, by rw [hc₂.rd, hc₂.wr]; simp,
      Offset.contains _ (by decide) (by omega) (by omega)⟩
  have hw₂ : InRegions u₂.wr ((L.F + BitVec.ofNat 32 (fT + j * P.F.H.D)).setWidth 64) P.F.H.D := by
    rw [eD, Offset.add_add]; exact hc₂.inFrW (by omega) (by omega) hL
  have hsep₂ : Region.Disjoint ⟨(L.F + BitVec.ofNat 32 fV).setWidth 64, P.F.H.D⟩
      ⟨(L.F + BitVec.ofNat 32 (fT + j * P.F.H.D)).setWidth 64, P.F.H.D⟩ := by
    rw [eS, eD, Offset.add_add]
    exact Offset.disjoint _ (.inl (by omega)) (by omega)
      (by omega)
  have hsf₂ : Safe L ⟨(L.F + BitVec.ofNat 32 (fT + j * P.F.H.D)).setWidth 64, P.F.H.D⟩ := by
    rw [eD, Offset.add_add]; exact safe_high L (by omega) (by omega)
  have hS₂ : (L.F + BitVec.ofNat 32 fV).toNat + P.F.H.D ≤ 2 ^ 32 := by
    rw [hL.frN (by decide)]; have := hL.e28; have := hL.e588; omega
  have hD₂ : (L.F + BitVec.ofNat 32 (fT + j * P.F.H.D)).toNat + P.F.H.D ≤ 2 ^ 32 := by
    rw [hL.frN (by omega)]; have := hL.e28; have := hL.e588; omega
  refine WP.seq (WP.mono (cpLoop_ok hL hc₂ (by omega) (by omega) hS₂ hD₂ hr₂ hw₂ hsep₂ hsf₂
      hsi₂ hbx₂ hcx₂) fun u₃ ⟨hc₃, hf₃, hb₃, _⟩ => ?_)
  rw [eD, hm₂] at hf₃ hb₃
  rw [eS] at hb₃
  have hl₃ : tlen L u₃.mem = BitVec.ofNat 32 (j * P.F.H.D) := by
    rw [← hl₁]
    exact hf₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [Offset.add_add]
      exact Offset.disjoint _ (.inl (by omega)) (by omega)
        (by omega)) (by decide)
  refine WP.mono (tStep_ok hL hT hc₃ hl₃ (by omega)) fun u₄ ⟨hc₄, hf₄, hl₄, hcf₄⟩ => ?_
  -- What the copy and the length's store keep.
  have kp : ∀ {o n : Nat}, 76 ≤ o → o + n ≤ 204 →
      Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 o) n = Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 o) n :=
    fun h₁ h₂ => by
      rw [bytesAt_frame hf₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega))
        (by omega),
        bytesAt_frame hf₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [Offset.add_add]
          exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by omega)]
  have hK : kOf P L u₄.mem = K := by
    rw [show kOf P L u₄.mem = Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 76) P.F.H.D from rfl,
      kp (by decide) (by omega)]
    exact hk₁.trans hI.k
  refine ⟨⟨hc₄, ?_, hK, ?_, ?_, ?_, ?_⟩, by rw [hcf₄, hjD]⟩
  · refine ((hI.frame.trans (hf₁.sub fun r hr => ?_)).trans (hf₃.sub fun r hr => ?_)).trans (hf₄.sub fun r hr => ?_)
    · simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨⟨L.B, 204⟩, by simp, sub_refl _⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨kAddr L, 136⟩, by simp, Offset.sub_base _ (by omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, by simp, sub_refl _⟩
  · rw [show vOf P L u₄.mem = Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 140) P.F.H.D from rfl,
      kp (by decide) (by omega), genT_succ]
    show vOf P L u₁.mem = _
    rw [hv₁, hI.k, hI.v]
  · rw [hl₄, hjD]
  · show Spec.Sha256.bytesAt u₄.mem (kAddr L) ((j + 1) * P.F.H.D) = _
    rw [hjD, Proof.Hmac.Common.bytesAt_add,
      bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inr (by omega)) (by omega)
          (by omega)) (by omega),
      bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [Offset.add_add]
        exact Offset.disjoint _ (.inr (by omega)) (by omega)
          (by omega)) (by omega),
      hb₃, bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (Nat.le_refl _) (by omega)) (by omega),
      ht₁, show Spec.Sha256.bytesAt u.mem (kAddr L) (j * P.F.H.D) = _ from hI.t, genT_succ]
    rw [show Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 (76 + fV)) P.F.H.D = vOf P L u₁.mem from rfl, hv₁,
      hI.k, hI.v]
  · rw [hk₁, hI.k] at hS₁
    refine (hS₁.frame hf₃ fun r hr => ?_).frame hf₄ fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      rw [Offset.add_add]
      exact (hL.stk_scr (d := 76 + fT + j * P.F.H.D) (n := P.F.H.D) (by omega) (by decide)).symm
    · simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_scr (d := 76 + fTlen) (n := 4) (by omega) (by decide)).symm

/-- The number of `V`s in a candidate: `⌈Q / D⌉`. -/
abbrev RfcHash.nV (P : RfcHash) : Nat := (P.Q + P.F.H.D - 1) / P.F.H.D

theorem nV_lt (P : RfcHash) (j : Nat) : j + 1 < P.nV ↔ (j + 1) * P.F.H.D < P.Q := by
  obtain ⟨-, -, -, -, hD16, -, -, -, -, -, -, -, -, -, -, hQ8, -, -, -⟩ := P.sizes
  rw [RfcHash.nV, Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by omega), Nat.succ_mul (j + 1)]
  omega

theorem nV_facts (P : RfcHash) : 1 ≤ P.nV ∧ P.nV * P.F.H.D ≤ P.Q + P.F.H.D - 1 ∧ P.Q ≤ P.nV * P.F.H.D := by
  obtain ⟨-, -, -, -, hD16, -, -, -, -, -, -, -, -, -, -, hQ8, -, -, -⟩ := P.sizes
  have e₁ := Nat.div_mul_le_self (P.Q + P.F.H.D - 1) P.F.H.D
  have e₂ := Nat.lt_mul_div_succ (P.Q + P.F.H.D - 1) (show 0 < P.F.H.D by omega)
  have e₃ : 1 ≤ P.nV := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  simp only [RfcHash.nV] at e₃ ⊢
  generalize (P.Q + P.F.H.D - 1) / P.F.H.D = N at e₁ e₂ e₃ ⊢
  rw [Nat.mul_succ, Nat.mul_comm] at e₂
  omega

/-- RFC 6979's number of blocks is `⌈Q / D⌉`. -/
theorem nV_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.F.H.D = P.nV := by
  obtain ⟨-, -, -, -, hD16, -, -, -, -, -, -, -, -, -, -, hQ8, -, -, -⟩ := P.sizes
  have hl := P.R.nBits_len
  have e₁ := Nat.div_mul_le_self (P.Q + P.F.H.D - 1) P.F.H.D
  have e₂ := Nat.lt_mul_div_succ (P.Q + P.F.H.D - 1) (show 0 < P.F.H.D by omega)
  rw [Spec.Ecdsa.Rfc6979.blocks]
  simp only [RfcHash.nV, RfcHash.Q] at e₁ e₂ hQ8 ⊢
  generalize (P.R.E.C.len + P.F.H.D - 1) / P.F.H.D = N at e₁ e₂ ⊢
  rw [Nat.mul_succ, Nat.mul_comm] at e₂
  have h₁ : N * (8 * P.F.H.D) = 8 * (N * P.F.H.D) := Nat.mul_left_comm _ _ _
  have h₂ : (N + 1) * (8 * P.F.H.D) = 8 * (N * P.F.H.D) + 8 * P.F.H.D := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_left_comm]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- The loop: `nV` `V`s. -/
theorem loop_ok (hL : L.Ok) (hT : TabL P L) {t₀ : State} {K V₀ : List Byte} {u : State}
    (hI : CI P L g m₀ t₀ K V₀ 0 u) :
    WP isa (.loop (cfgOf P).candStep .b) u (CI P L g m₀ t₀ K V₀ P.nV) := by
  obtain ⟨hN1, hND, -⟩ := nV_facts P
  obtain ⟨-, -, -, -, -, hD64, -, -, -, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  refine WP.loop (M := isa) (fun (n : Nat) (s : State) => ∃ j, n = P.nV - j ∧ j < P.nV ∧ CI P L g m₀ t₀ K V₀ j s)
    ?_ (P.nV - 0) u ⟨0, rfl, hN1, hI⟩
  rintro n s ⟨j, rfl, hj, hIj⟩
  have hb : (j + 1) * P.F.H.D ≤ 136 :=
    Nat.le_trans (Nat.mul_le_mul (show j + 1 ≤ P.nV by omega) (Nat.le_refl P.F.H.D)) (by omega)
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
  obtain ⟨-, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  refine WP.mono (tInit_ok hL hc) fun u₀ ⟨hc₀, hf₀, hl₀⟩ => ?_
  have hfV : fV = 64 := rfl
  have hfT : fT = 376 := rfl
  have hfTl : fTlen = 152 := rfl
  have kv0 : ∀ {o : Nat}, 76 ≤ o → o + P.F.H.D ≤ 204 →
      Spec.Sha256.bytesAt u₀.mem (L.B + BitVec.ofNat 64 o) P.F.H.D =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 o) P.F.H.D := fun h₁ h₂ =>
    bytesAt_frame hf₀ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega))
      (by omega)
  exact
    { ctx := hc₀
      frame := hf₀.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, by simp, sub_refl _⟩
      k := kv0 (by decide) (by omega)
      v := kv0 (by decide) (by omega)
      len := by rw [hl₀, Nat.zero_mul]; rfl
      t := by simp [Spec.Sha256.bytesAt, Spec.Ecdsa.Rfc6979.genT]
      saved := hS.frame hf₀ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hL.stk_scr (by omega) (by decide)).symm }

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (Spec.Sha256.bytesAt m p n).length = n := by
  simp [Spec.Sha256.bytesAt]

/-- The candidate: `nV` successive `V = HMAC_K(V)`, and `k`, whose number is
`bits2int` of their concatenation, where `core` reads it. -/
theorem cand_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g m₀ t)
    (hS : SavedK P L t.mem (kOf P L t.mem)) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ Frame (CW L) t.mem u.mem ∧ kOf P L u.mem = kOf P L t.mem ∧
      vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).2 ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kAddr L) P.Q) =
        Spec.Ecdsa.Rfc6979.bits2int P.R.E.C
          (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 ∧
      SavedK P L u.mem (kOf P L t.mem) := by
  obtain ⟨-, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  have hl := P.R.nBits_len
  obtain ⟨-, hND, hQN⟩ := nV_facts P
  have hfV : fV = 64 := rfl
  have hfT : fT = 376 := rfl
  have hfTl : fTlen = 152 := rfl
  rw [Cfg.cand]
  refine WP.seq (WP.mono (tInit_ci hL hc hS) fun u₀ hI0 => ?_)
  refine WP.seq (WP.mono (loop_ok hL hT hI0) fun u₁ hI₁ => ?_)
  have hTl := genT_length P (kOf P L t.mem) P.nV (vOf P L t.mem)
  have hbits : Spec.Ecdsa.Rfc6979.bits2int P.R.E.C
      (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 =
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u₁.mem (kAddr L) P.Q) >>> P.R.sh := by
    rw [Spec.Ecdsa.Rfc6979.bits2int, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega)
      (by rw [hTl]; exact hQN),
      show (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nV (vOf P L t.mem)).1 =
        Spec.Sha256.bytesAt u₁.mem (kAddr L) (P.nV * P.F.H.D) from hI₁.t.symm,
      ← bytesAt_take _ _ hQN, show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = P.R.sh by rw [hl.2.2]]
  cases hb : P.R.big
  · have hsh : P.R.sh = 0 := by have := (P.R.sizesA hb).2.2.1; omega
    rw [show (cfgOf P).candTop = .block [] by simp only [Cfg.candTop, show (cfgOf P).big = false from hb,
      Bool.false_eq_true, ite_false], WP.block_nil_iff]
    exact ⟨hI₁.ctx, hI₁.frame, hI₁.k, hI₁.v, by rw [hbits, hsh, Nat.shiftRight_zero], hI₁.saved⟩
  · have hsh8 : P.R.sh < 8 := by omega
    have hsh0 : P.R.sh ≠ 0 := by have := (P.R.sizesW hb); omega
    refine WP.mono (candTop_ok hL hb hsh0 hsh8 hI₁.ctx) fun u ⟨hcu, hf, hbu⟩ => ?_
    have kv : ∀ {o : Nat}, 76 ≤ o → o + P.F.H.D ≤ 204 →
        Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 o) P.F.H.D =
          Spec.Sha256.bytesAt u₁.mem (L.B + BitVec.ofNat 64 o) P.F.H.D := fun h₁ h₂ =>
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr (by omega) (by decide)
        · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by omega)
    refine ⟨hcu, hI₁.frame.trans (hf.sub fun r hr => ?_), (kv (by decide) (by omega)).trans hI₁.k,
      (kv (by decide) (by omega)).trans hI₁.v, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨L.SCR, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨⟨kAddr L, 136⟩, by simp, Region.sub_prefix (by omega)⟩
    · rw [hbu, hbits,
        ofBytes_toBytes _ _ (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by
          have := ofBytes_lt (Spec.Sha256.bytesAt u₁.mem (kAddr L) P.Q)
          rwa [length_bytesAt] at this))]
    · refine hI₁.saved.frame hf fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
      · exact (hL.stk_scr (by omega) (by decide)).symm

end VG.Proof.Ecdsa.Rfc6979.X86
