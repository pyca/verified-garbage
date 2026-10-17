module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Steps
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Wide
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Setup
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Core
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.X25519.X86.Column

/-!
# Deterministic ECDSA on x86 (32-bit): a candidate's `V`s

The candidate (`Cfg.cand`): `nb` times `V = HMAC_K(V)`, each `V`'s 64 bytes
copied to the candidate's place at an offset that grows by `D`, so that its
first `i D` bytes are the first `i` `V`s (`CandInv`, `candIter_ok`), RFC 6979's
`T` (`genT_succ`); the loop stops after `nb` (`candLoop_ok`). Then `k` for
`core` is `T`'s first `Q` bytes, shifted right by `sh` bits for P-521
(`cand_ok`), whose number is `bits2int` of `T`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Mont.X86 (wp_movS wp_addS)
open VG.Impl.Pbkdf2.Stream.X86 (at_)

theorem genT_cons (H : Spec.Hmac.HashFunction) (K V : List Byte) (n : Nat) :
    Spec.Ecdsa.Rfc6979.genT H K (n + 1) V =
      (Spec.Hmac.hmac H K V ++ (Spec.Ecdsa.Rfc6979.genT H K n (Spec.Hmac.hmac H K V)).1,
        (Spec.Ecdsa.Rfc6979.genT H K n (Spec.Hmac.hmac H K V)).2) := rfl

/-- `genT` appends each `V` after the previous ones. -/
theorem genT_succ (H : Spec.Hmac.HashFunction) (K : List Byte) : ∀ (i : Nat) (V : List Byte),
    Spec.Ecdsa.Rfc6979.genT H K (i + 1) V =
      ((Spec.Ecdsa.Rfc6979.genT H K i V).1 ++ Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K i V).2,
        Spec.Hmac.hmac H K (Spec.Ecdsa.Rfc6979.genT H K i V).2)
  | 0, V => by simp [Spec.Ecdsa.Rfc6979.genT]
  | i + 1, V => by
    rw [genT_cons, genT_succ H K i (Spec.Hmac.hmac H K V), genT_cons H K V i, List.append_assoc]

variable {P : RfcHash} {L : Lay P.I.hashLen} {g : Reg → BitVec 32} {m₀ : Mem}

theorem genT_length (P : RfcHash) (K V : List Byte) : ∀ i,
    (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H K i V).1.length = i * P.F.H.D
  | 0 => by simp [Spec.Ecdsa.Rfc6979.genT]
  | i + 1 => by
    rw [genT_succ, List.length_append, genT_length P K V i]
    have := mac_length P K (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H K i V).2
    simp only [RfcHash.mac] at this
    rw [this, Nat.succ_mul]

/-- What a candidate changes: `scratch`, the stack below the frame, `K` and
`V`, the offset and count of its `V`s, and the candidate. -/
abbrev CW {dn : Nat} (L : Lay dn) : List Region :=
  [L.SCR, ⟨L.B, 204⟩, ⟨L.B + BitVec.ofNat 64 236, 8⟩, ⟨L.B + BitVec.ofNat 64 408, 128⟩]

theorem kvw_cw : ∀ r ∈ KVW L, ∃ r' ∈ CW L, Region.Sub r r' := fun r hr => ⟨r, by
  simp only [CW, KVW, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with h | h <;> simp [h], sub_refl _⟩

/-- After `i` of the candidate's `V`s, from `t`. -/
structure CandInv (P : RfcHash) (L : Lay P.I.hashLen) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) (i : Nat)
    (u : State) : Prop where
  ctx : Ctx L g m₀ u
  frame : Frame (CW L) t.mem u.mem
  k : kOf P L u.mem = kOf P L t.mem
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) i (vOf P L t.mem)).2
  c : Spec.Sha256.bytesAt u.mem (kAddr L) (i * P.F.H.D) =
    (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) i (vOf P L t.mem)).1
  off : u.mem.readW (L.B + BitVec.ofNat 64 236) 32 = BitVec.ofNat 32 (i * P.F.H.D)
  cnt2 : u.mem.readW (L.B + BitVec.ofNat 64 240) 32 = BitVec.ofNat 32 (P.nb - i)
  le : i ≤ P.nb

/-- `[esp + o]`, for `o` in the frame. -/
theorem frA (hL : L.Ok) {o : Nat} (ho : o < 488) : addr L.F o = L.B + BitVec.ofNat 64 (76 + o) := hL.addrF ho

/-- The offset 0 and the count `nb`. -/
theorem candInit_ok (hL : L.Ok) (hk : Fits P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block candInit) t (CandInv P L g m₀ t 0) := by
  have nB := hL.nB
  have a₁ : addr L.F 160 = L.B + BitVec.ofNat 64 236 := frA hL (by decide)
  have a₂ : addr L.F 164 = L.B + BitVec.ofNat 64 240 := frA hL (by decide)
  simp only [candInit, stk, pOff, pCnt2, pNb]
  refine wp_movi fun u₁ v₁ => wp_stm (B := L.F) (by rw [v₁.other _ (by decide), hc.esp])
    (by rw [v₁.wr, a₁]; exact hc.inFrW (by omega) (by omega) hL) fun u₂ v₂ => ?_
  rw [a₁, v₁.gpr, v₁.mem] at v₂
  have hf₂ : Frame [⟨L.B + BitVec.ofNat 64 236, 4⟩] t.mem u₂.mem := by
    rw [v₂.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hc₂ : Ctx L g m₀ u₂ := hc.keep (hsy := by rw [v₂.syms, v₁.syms]) hL (by rw [v₂.rd, v₁.rd])
    (by rw [v₂.wr, v₁.wr]) (by rw [v₂.gpr, v₁.other _ (by decide)]) hf₂
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_cnt L (by omega) (by omega))
  refine wp_movS (hc₂.readPrm hL (i := 7) (by decide) rfl) fun u₃ v₃ _ => ?_
  refine wp_stm (B := L.F) (by rw [v₃.other _ (by decide), hc₂.esp])
    (by rw [v₃.wr, a₂]; exact hc₂.inFrW (by omega) (by omega) hL) fun u₄ v₄ => WP.block_nil ?_
  rw [a₂, v₃.gpr, v₃.mem] at v₄
  have hf₄ : Frame [⟨L.B + BitVec.ofNat 64 240, 4⟩] u₂.mem u₄.mem := by
    rw [v₄.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hf : Frame (CW L) t.mem u₄.mem := (hf₂.sub fun r hr => ⟨⟨L.B + BitVec.ofNat 64 236, 8⟩, by simp [CW], by
    simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩).trans
    (hf₄.sub fun r hr => ⟨⟨L.B + BitVec.ofNat 64 236, 8⟩, by simp [CW], by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)⟩)
  have kv : ∀ o, 76 ≤ o → o + 64 ≤ 204 →
      Spec.Sha256.bytesAt u₄.mem (L.B + BitVec.ofNat 64 o) P.F.H.D =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 o) P.F.H.D := fun o h₁ h₂ => by
    rw [bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by omega))
        (by nums),
      bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by nums) (by nums) (by omega))
        (by nums)]
  refine ⟨hc₂.keep (hsy := by rw [v₄.syms, v₃.syms]) hL (by rw [v₄.rd, v₃.rd]) (by rw [v₄.wr, v₃.wr])
      (by rw [v₄.gpr, v₃.other _ (by decide)]) hf₄
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_cnt L (by omega) (by omega)),
    hf, kv 76 (by omega) (by omega), kv 140 (by omega) (by omega), by simp [Spec.Sha256.bytesAt,
      Spec.Ecdsa.Rfc6979.genT], ?_, ?_, Nat.zero_le _⟩
  · rw [v₄.mem, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), v₂.mem,
      Mem.readW_writeW_self32]; simp
  · rw [v₄.mem, Mem.readW_writeW_self32, Nat.sub_zero, ← pv_sizeVal hk 7 (by decide)]; rfl

theorem cnt_sub {T i : Nat} (hi : i < T) :
    BitVec.ofNat 32 (T - i) - 1 = BitVec.ofNat 32 (T - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 32).toNat = 1 := rfl
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, h1]
  omega

theorem cnt_ne {T i : Nat} (hT : T < 2 ^ 32) : BitVec.ofNat 32 (T - (i + 1)) ≠ 0 ↔ i + 1 < T := by
  rw [Ne, ← BitVec.toNat_inj]
  have h0 : (0 : BitVec 32).toNat = 0 := rfl
  simp only [BitVec.toNat_ofNat, h0]
  omega

/-- An address at `F + x` and an offset. -/
theorem addrFx (hL : L.Ok) {x o : Nat} (h : x + o < 488) :
    addr (L.F + BitVec.ofNat 32 x) o = L.B + BitVec.ofNat 64 (76 + x + o) := by
  rw [addr_eq (by rw [hL.frN (by omega)]; have := hL.e536; have := hL.e28; omega), hL.frv (by omega), Offset.add_add]

/-- Where the next `V` goes: `edi ← esp + 332 + off`. -/
theorem candAt_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {x : Nat}
    (hoff : u.mem.readW (L.B + BitVec.ofNat 64 236) 32 = BitVec.ofNat 32 x) :
    WP isa (.block candAt) u (Upd L g m₀ u .edi (L.F + BitVec.ofNat 32 (332 + x))) := by
  rw [candAt, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .edi) (by decide) fC) fun u₁ h₁ => ?_
  refine wp_addS (v := BitVec.ofNat 32 x) (by
      rw [show (.mem (stk pOff) : Src) = .mem ⟨.esp, 160⟩ from rfl,
        readSrc_mem h₁.ctx.esp (by rw [frA hL (by decide)]; exact h₁.ctx.inFr (by omega) (by omega) hL),
        frA hL (by decide), h₁.mem, hoff]) fun u₂ v₂ _ => WP.block_nil ?_
  rw [h₁.val, BitVec.add_assoc, BitVec.ofNat_add_ofNat] at v₂
  exact ⟨h₁.ctx.regs hL v₂.rd v₂.wr v₂.mem (v₂.other _ (by decide)) v₂.syms, v₂.mem.trans h₁.mem, v₂.gpr,
    fun r hr => (v₂.other r hr).trans (h₁.keep r hr)⟩

/-- `V`'s 64 bytes at the offset `x`, the next offset, and one `V` fewer. -/
theorem candStep_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {x c : Nat} (hx : x ≤ 64)
    (hdi : u.gpr .edi = L.F + BitVec.ofNat 32 (332 + x))
    (hoff : u.mem.readW (L.B + BitVec.ofNat 64 236) 32 = BitVec.ofNat 32 x)
    (hcnt : u.mem.readW (L.B + BitVec.ofNat 64 240) 32 = BitVec.ofNat 32 c) :
    WP isa (.block candStep) u fun u' => Ctx L g m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 (408 + x), 64⟩, ⟨L.B + BitVec.ofNat 64 236, 8⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (408 + x)) 64 =
        Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 140) 64 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 236) 32 = BitVec.ofNat 32 x + L.pv 0 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 240) 32 = BitVec.ofNat 32 c - 1 ∧
      u'.zf = some (BitVec.ofNat 32 c - 1 == 0) := by
  have nB := hL.nB
  rw [candStep, copyV, WP.block_append_iff]
  refine WP.mono_syms (copyN_ok (S := L.F) (D := L.F + BitVec.ofNat 32 (332 + x)) (SA := L.B + BitVec.ofNat 64 140)
    (DA := L.B + BitVec.ofNat 64 (408 + x)) (so := fV) (d := 0) (K := 16) (src := .esp) (dst := .edi) (by decide)
    (by decide) (fun j hj => fr_addr hL (by simp only [fV]; omega))
    (fun j hj => by rw [addrFx hL (by omega), Offset.add_add]; congr 2; omega)
    (Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega) 16 (Nat.le_refl _) u hc.esp hdi
    (fun j hj => by rw [Offset.add_add]; exact hc.inFr (by omega) (by omega) hL)
    (fun j hj => by rw [Offset.add_add]; exact hc.inFrW (by omega) (by omega) hL))
    fun u₁ ⟨hrd₁, hwr₁, hg₁, hf₁, hb₁⟩ hsy₁ => ?_
  have hc₁ : Ctx L g m₀ u₁ := hc.keep (hsy := hsy₁) hL hrd₁ hwr₁ (hg₁ _ (by decide)) hf₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_high L (by omega) (by omega))
  have k₁ : ∀ o, 236 ≤ o → o + 4 ≤ 244 → u₁.mem.readW (L.B + BitVec.ofNat 64 o) 32 = u.mem.readW (L.B + BitVec.ofNat 64 o) 32 :=
    fun o h₁ h₂ => hf₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)
  have a₁ : addr L.F 160 = L.B + BitVec.ofNat 64 236 := frA hL (by decide)
  have a₂ : addr L.F 164 = L.B + BitVec.ofNat 64 240 := frA hL (by decide)
  simp only [stk, pOff, pCnt2]
  refine wp_ldm hc₁.esp (by rw [a₁]; exact hc₁.inFr (by omega) (by omega) hL) fun u₂ v₂ => ?_
  have hc₂ : Ctx L g m₀ u₂ := hc₁.regs hL v₂.rd v₂.wr v₂.mem (v₂.other _ (by decide)) v₂.syms
  refine wp_addS (hc₂.readPrm hL (i := 0) (by decide) rfl) fun u₃ v₃ _ => ?_
  refine wp_stm (B := L.F) (by rw [v₃.other _ (by decide), v₂.other _ (by decide), hc₁.esp])
    (by rw [a₁, v₃.wr, v₂.wr]; exact hc₁.inFrW (by omega) (by omega) hL) fun u₄ v₄ => ?_
  rw [a₁, v₃.gpr, v₂.gpr, a₁, k₁ 236 (by omega) (by omega), hoff] at v₄
  have hm₄ : u₄.mem = u₁.mem.writeW (L.B + BitVec.ofNat 64 236) (BitVec.ofNat 32 x + L.pv 0) := by
    rw [v₄.mem, v₃.mem, v₂.mem]
  have hf₄ : Frame [⟨L.B + BitVec.ofNat 64 236, 4⟩] u₁.mem u₄.mem := by
    rw [hm₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hc₄ : Ctx L g m₀ u₄ := hc₁.keep (hsy := by rw [v₄.syms, v₃.syms, v₂.syms]) hL (by rw [v₄.rd, v₃.rd, v₂.rd])
    (by rw [v₄.wr, v₃.wr, v₂.wr]) (by rw [v₄.gpr, v₃.other _ (by decide), v₂.other _ (by decide)]) hf₄
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_cnt L (by omega) (by omega))
  refine wp_ldm hc₄.esp (by rw [a₂]; exact hc₄.inFr (by omega) (by omega) hL) fun u₅ v₅ => ?_
  refine wp_subi fun u₆ v₆ _ _ => ?_
  refine wp_stm (B := L.F) (by rw [v₆.other _ (by decide), v₅.other _ (by decide), hc₄.esp])
    (by rw [a₂, v₆.wr, v₅.wr]; exact hc₄.inFrW (by omega) (by omega) hL) fun u₇ v₇ => ?_
  refine wp_test fun u₈ v₈ zf₈ => WP.block_nil ?_
  have c₄ : u₄.mem.readW (L.B + BitVec.ofNat 64 240) 32 = BitVec.ofNat 32 c := by
    rw [hm₄, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
      k₁ 240 (by omega) (by omega), hcnt]
  rw [a₂, v₆.gpr, v₅.gpr, a₂, c₄] at v₇
  have hm₇ : u₇.mem = u₄.mem.writeW (L.B + BitVec.ofNat 64 240) (BitVec.ofNat 32 c - 1) := by
    rw [v₇.mem, v₆.mem, v₅.mem]
  have hf₇ : Frame [⟨L.B + BitVec.ofNat 64 240, 4⟩] u₄.mem u₇.mem := by
    rw [hm₇]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hm₈ : u₈.mem = u₇.mem := v₈.mem
  refine ⟨(hc₄.keep (hsy := by rw [v₇.syms, v₆.syms, v₅.syms]) hL (by rw [v₇.rd, v₆.rd, v₅.rd])
      (by rw [v₇.wr, v₆.wr, v₅.wr]) (by rw [v₇.gpr, v₆.other _ (by decide), v₅.other _ (by decide)]) hf₇
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_cnt L (by omega) (by omega))).regs hL
      v₈.rd v₈.wr hm₈ (by rw [v₈.gpr]) v₈.syms, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm₈]
    refine ((hf₁.sub fun r hr => ⟨_, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr; exact sub_refl _⟩).trans
      (hf₄.sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩)).trans
      (hf₇.sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega) (by omega)⟩)
  · rw [hm₈, bytesAt_frame hf₇ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by omega), bytesAt_frame hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by omega)]
    exact hb₁
  · rw [hm₈, hm₇, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), hm₄,
      Mem.readW_writeW_self32]
  · rw [hm₈, hm₇, Mem.readW_writeW_self32]
  · rw [zf₈, v₇.gpr, v₆.gpr, v₅.gpr, BitVec.and_self, a₂, c₄]

/-- One of the candidate's `V`s. -/
theorem candIter_ok (hL : L.Ok) (hk : Fits P L) {t u : State} {i : Nat} (hi : i < P.nb)
    (h : CandInv P L g m₀ t i u) :
    WP isa (.seq (cfgOf P).hmacV (.seq (.block candAt) (.block candStep))) u fun u' =>
      CandInv P L g m₀ t (i + 1) u' ∧ isa.eval .ne u' = some (decide (i + 1 < P.nb)) := by
  have nB := hL.nB
  have hnb := P.nb_facts
  have hiD : i * P.F.H.D ≤ 64 :=
    Nat.le_trans (Nat.mul_le_mul_right _ (show i ≤ P.nb - 1 by omega)) hnb.2.2.1
  have hD : P.F.H.D ≤ 64 := by nums
  refine WP.seq (WP.mono (hmacV_ok hL hk h.ctx) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁⟩ => ?_)
  have kvw : ∀ {d n : Nat}, 236 ≤ d → d + n ≤ 536 → ∀ r ∈ KVW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r :=
    fun h₁ h₂ r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR h₂
      · exact Offset.disjoint_base _ (by omega) (by omega)
  have off₁ : u₁.mem.readW (L.B + BitVec.ofNat 64 236) 32 = BitVec.ofNat 32 (i * P.F.H.D) :=
    (hf₁.readW (Region.contains_self _ _) (kvw (n := 4) (by omega) (by omega)) (by decide)).trans h.off
  have cnt₁ : u₁.mem.readW (L.B + BitVec.ofNat 64 240) 32 = BitVec.ofNat 32 (P.nb - i) :=
    (hf₁.readW (Region.contains_self _ _) (kvw (n := 4) (by omega) (by omega)) (by decide)).trans h.cnt2
  have c₁ : Spec.Sha256.bytesAt u₁.mem (kAddr L) (i * P.F.H.D) = Spec.Sha256.bytesAt u.mem (kAddr L) (i * P.F.H.D) :=
    bytesAt_frame hf₁ (kvw (by omega) (by omega)) (by omega)
  refine WP.seq (WP.mono (candAt_ok hL hc₁ off₁) fun u₂ h₂ => ?_)
  rw [← h₂.mem] at off₁ cnt₁
  refine WP.mono (candStep_ok hL h₂.ctx hiD h₂.val off₁ cnt₁) fun u₃ ⟨hc₃, hf₃, hb₃, ho₃, hn₃, hz₃⟩ => ⟨?_, ?_⟩
  · have d₃ : ∀ {d n : Nat}, 76 ≤ d → d + n ≤ 204 →
        Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 d) n = Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 d) n :=
      fun h₁ h₂ => bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega)
    have hk₃ : kOf P L u₃.mem = kOf P L u₁.mem := by rw [kOf, keyOf, d₃ (by omega) (by omega), h₂.mem]
    have hv₃ : vOf P L u₃.mem = vOf P L u₁.mem := by rw [vOf, d₃ (by omega) (by omega), h₂.mem]
    refine ⟨hc₃, ?_, hk₃.trans (hk₁.trans h.k), ?_, ?_, ?_, ?_, by omega⟩
    · refine (h.frame.trans (hf₁.sub kvw_cw)).trans (h₂.mem ▸ hf₃.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨L.B + BitVec.ofNat 64 408, 128⟩, by simp [CW], Offset.sub _ (by omega) (by omega)⟩
      · exact ⟨⟨L.B + BitVec.ofNat 64 236, 8⟩, by simp [CW], sub_refl _⟩
    · rw [hv₃, hv₁, h.k, h.v, genT_succ]
    · rw [Nat.succ_mul, Proof.Hmac.Common.bytesAt_add, genT_succ, kAddr, Offset.add_add]
      congr 1
      · rw [bytesAt_frame hf₃ (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by omega),
          h₂.mem, c₁, h.c]
      · rw [bytesAt_take _ _ (k := 64) hD, hb₃, ← bytesAt_take _ _ hD, h₂.mem]
        show vOf P L u₁.mem = _
        rw [hv₁, h.k, h.v]
    · rw [ho₃, show L.pv 0 = BitVec.ofNat 32 P.F.H.D from rfl, BitVec.ofNat_add_ofNat, Nat.succ_mul]
    · rw [hn₃, cnt_sub hi]
  · show u₃.zf.map (!·) = _
    rw [hz₃, cnt_sub hi]
    have := cnt_ne (T := P.nb) (i := i) (by omega)
    by_cases hc : i + 1 < P.nb
    · have h1 := this.mpr hc
      simp only [hc, decide_true, Option.map_some, beq_eq_false_iff_ne.mpr h1, Bool.not_false]
    · have h0 : BitVec.ofNat 32 (P.nb - (i + 1)) = 0 := Classical.not_not.mp (mt this.mp hc)
      simp only [hc, decide_false, Option.map_some, h0, beq_self_eq_true, Bool.not_true]

/-- The candidate's `V`s: `nb` of them. -/
theorem candLoop_ok (hL : L.Ok) (hk : Fits P L) {t u : State} (h : CandInv P L g m₀ t 0 u) :
    WP isa (.loop (.seq (cfgOf P).hmacV (.seq (.block candAt) (.block candStep))) .ne) u
      (CandInv P L g m₀ t P.nb) := by
  have hnb := P.nb_facts
  refine WP.loop (M := isa) (fun n s => 1 ≤ n ∧ n ≤ P.nb ∧ CandInv P L g m₀ t (P.nb - n) s) ?_ P.nb u
    ⟨hnb.1, Nat.le_refl _, by rw [Nat.sub_self]; exact h⟩
  rintro n s ⟨h₁, h₂, hs⟩
  refine WP.mono (candIter_ok hL hk (by omega) hs) fun s' ⟨hs', he⟩ => ?_
  by_cases hc : P.nb - n + 1 < P.nb
  · refine .inr ⟨by rw [he, decide_eq_true hc], n - 1, by omega, by omega, by omega, ?_⟩
    rwa [show P.nb - (n - 1) = P.nb - n + 1 by omega]
  · refine .inl ⟨by rw [he, decide_eq_false hc], ?_⟩
    rwa [show P.nb = P.nb - n + 1 by omega]

/-- The candidate: `nb` `V`s, and `k`, whose number is `bits2int` of the
candidate, where `core` reads it. -/
theorem cand_ok (hL : L.Ok) (hk : Fits P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ Frame (CW L) t.mem u.mem ∧ kOf P L u.mem = kOf P L t.mem ∧
      vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nb (vOf P L t.mem)).2 ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kAddr L) P.Q) =
        Spec.Ecdsa.Rfc6979.bits2int P.R.E.C
          (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nb (vOf P L t.mem)).1 := by
  have nB := hL.nB
  have hnb := P.nb_facts
  have hl := P.R.nBits_len
  have hT : (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nb (vOf P L t.mem)).1.length = P.nb * P.F.H.D :=
    genT_length P _ _ _
  refine WP.seq (WP.mono (candInit_ok hL hk hc) fun u₀ h₀ => ?_)
  refine WP.seq (WP.mono (candLoop_ok hL hk h₀) fun u₁ h₁ => ?_)
  have hb₁ : Spec.Sha256.bytesAt u₁.mem (kAddr L) P.Q =
      (Spec.Ecdsa.Rfc6979.genT P.ok.hH.SH.H (kOf P L t.mem) P.nb (vOf P L t.mem)).1.take P.Q := by
    rw [bytesAt_take _ _ hnb.2.1, h₁.c]
  cases hW : P.R.wide
  · have h0 := P.sh0 hW
    have hB : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := by show _ = 8 * P.R.E.C.len; omega
    simp only [show (cfgOf P).sh = 0 from h0]
    refine WP.block_nil ⟨h₁.ctx, h₁.frame, h₁.k, h₁.v, ?_⟩
    rw [hb₁, Spec.Ecdsa.Rfc6979.bits2int, hashToInt_takeQ hB (by rw [hT]; exact hnb.2.1)]
  · obtain ⟨-, hQ66, h7⟩ := P.sizesW hW
    simp only [show (cfgOf P).sh = 7 from h7, show (7 : Nat) = 0 ↔ False by decide]
    refine WP.seq (WP.mono (arg_ok hL h₁.ctx (d := .edi) (by decide) (i := 4) (by omega)) fun u₂ h₂ => ?_)
    refine WP.mono (conv_ok hL hW h₂.ctx h₂.val (o := fC) (s := 7) (by decide) (by decide) (by decide) (by decide))
      fun u₃ ⟨hc₃, _, hf₃, hb₃⟩ => ⟨hc₃, ?_, ?_, ?_, ?_⟩
    · refine h₁.frame.trans (h₂.mem ▸ hf₃.sub fun r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨L.SCR, by simp [CW], Offset.sub_base _ (by omega)⟩
      · exact ⟨⟨L.B + BitVec.ofNat 64 408, 128⟩, by simp [CW], Region.sub_prefix (by omega)⟩
    · have : kOf P L u₃.mem = kOf P L u₂.mem := bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr (by nums) (by omega)
        · exact Offset.disjoint _ (by simp only [fC]; nums) (by nums) (by simp only [fC]; omega)) (by nums)
      rw [this, h₂.mem, h₁.k]
    · have : vOf P L u₃.mem = vOf P L u₂.mem := bytesAt_frame hf₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.stk_scr (by nums) (by omega)
        · exact Offset.disjoint _ (by simp only [fC]; nums) (by nums) (by simp only [fC]; omega)) (by nums)
      rw [this, h₂.mem, h₁.v]
    · have hb₃' := hb₃
      simp only [fC, show 76 + 332 = 408 from rfl] at hb₃'
      have hx : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 408) P.Q) >>> 7 <
          2 ^ (8 * P.Q) := Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (by
        have := ofBytes_lt (Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 408) P.Q)
        rwa [length_bytesAt] at this)
      rw [kAddr, hb₃', ofBytes_toBytes _ _ hx, h₂.mem, show L.B + BitVec.ofNat 64 408 = kAddr L from rfl, hb₁,
        Spec.Ecdsa.Rfc6979.bits2int, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega)
          (by rw [hT]; exact hnb.2.1), show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = 7 by rw [← h7]; exact hl.2.2.symm]

end VG.Proof.Ecdsa.Rfc6979.X86
