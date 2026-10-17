module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Hmac
import VerifiedGarbage.Proof.Framework.WriteBytes
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.X25519.X86.Column

/-!
# Deterministic ECDSA on x86 (32-bit): the messages of steps d, f and h.3

`V ‖ b`, and `‖ d ‖ h` if `full`, at `scratch + 2256`, for `V` of `D` bytes
(`msg_ok`): `V`'s 64 bytes copied from the frame (`msgV_ok`), of which the
first `D` stay, then, from `scratch + D` (which `msgV` computes into `edi`),
the byte `b`, and the private key and `h` copied (`msgTail_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86
open VG.Impl.Pbkdf2.Stream.X86 (at_)
open VG.Proof.Mont.X86 (wp_movS wp_addS)

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `mov byte [m], r`. -/
theorem wp_store8 {r : Reg8} {m : MemOp} {a : Addr} (ha : s.ea m = a) (hw : InRegions s.wr a 1)
    (k : ∀ t, Mupd s t (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) t Q) :
    WP isa (.block (.store8 m r :: is)) s Q :=
  cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) })
    (by simp only [exec, ha, State.store8, hw, ite_true]) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

end

/-- A range of `scratch`, as the code addresses it from `scratch + x` in a register. -/
theorem scrx_addr (hL : L.Ok) {x o : Nat} (h : x + o < 8192) :
    addr (L.a3 + BitVec.ofNat 32 x) o = L.scr + BitVec.ofNat 64 (x + o) := by
  rw [addr_eq (by rw [hL.scrN (by omega_arith)]; have := hL.nc; omega_arith), hL.scrv (by omega_arith), Offset.add_add]

/-- A range of the frame, as the code addresses it from `esp`. -/
theorem fr_addr (hL : L.Ok) {o j : Nat} (h : o + 4 * j < 488) :
    addr L.F (o + 4 * j) = L.B + BitVec.ofNat 64 (76 + o) + BitVec.ofNat 64 (4 * j) := by
  rw [hL.addrF h, Offset.add_add, Nat.add_assoc]

/-- `4 K` bytes copied to `scratch + x + d` by `copyN`, with `scratch + x`
in `edi` and `Ctx` kept. -/
theorem copy_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : BitVec 32} {SA : Addr}
    (hs : u.gpr src = S) (hsr : src ≠ .eax) {x : Nat} (hdi : u.gpr .edi = L.a3 + BitVec.ofNat 32 x) {so d K : Nat}
    (hd : x + d + 4 * K ≤ 8192)
    (hSA : ∀ j < K, addr S (so + 4 * j) = SA + BitVec.ofNat 64 (4 * j))
    (hr : ∀ j < K, InRegions (u.rd ++ u.wr) (SA + BitVec.ofNat 64 (4 * j)) 4)
    (hsep : Region.Disjoint ⟨SA, 4 * K⟩ ⟨L.scr + BitVec.ofNat 64 (x + d), 4 * K⟩) :
    WP isa (.block (copyN K src so .edi d)) u fun u' => Ctx L g m₀ u' ∧ u'.rd = u.rd ∧ u'.wr = u.wr ∧
      (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.scr + BitVec.ofNat 64 (x + d), 4 * K⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (x + d)) (4 * K) = Spec.Sha256.bytesAt u.mem SA (4 * K) :=
  WP.mono_syms (copyN_ok (K := K) (by decide) hsr hSA (fun j hj => by
      rw [scrx_addr hL (by omega_arith), Offset.add_add, Nat.add_assoc]) hsep (by omega_arith) K
    (Nat.le_refl _) u hs hdi hr fun j hj => by rw [Offset.add_add]; exact hc.inScrW (by omega_arith))
    fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy =>
    ⟨hc.keep (hsy := hsy) hL hrd hwr (hg _ (by decide)) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega_arith)),
      hrd, hwr, hg, hf, hb⟩

/-- `Q` bytes copied to `scratch + x + d` by `copyBytes`, with `scratch + x`
in `edi` and `Ctx` kept. -/
theorem copyB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {src : Reg} {S : BitVec 32} {SA : Addr}
    (hs : u.gpr src = S) (hsr : src ≠ .eax) {x : Nat} (hdi : u.gpr .edi = L.a3 + BitVec.ofNat 32 x) {so d Q : Nat}
    (h4 : 4 ≤ Q) (hd : x + d + Q ≤ 8192) (hSA : ∀ j, j + 4 ≤ Q → addr S (so + j) = SA + BitVec.ofNat 64 j)
    (hr : ∀ j, j + 4 ≤ Q → InRegions (u.rd ++ u.wr) (SA + BitVec.ofNat 64 j) 4)
    (hsep : Region.Disjoint ⟨SA, Q⟩ ⟨L.scr + BitVec.ofNat 64 (x + d), Q⟩) :
    WP isa (.block (copyBytes Q src so .edi d)) u fun u' => Ctx L g m₀ u' ∧
      (∀ r, r ≠ .eax → u'.gpr r = u.gpr r) ∧ Frame [⟨L.scr + BitVec.ofNat 64 (x + d), Q⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.scr + BitVec.ofNat 64 (x + d)) Q = Spec.Sha256.bytesAt u.mem SA Q :=
  WP.mono_syms (copyBytes_ok (by decide) hsr hSA (fun j hj => by
      rw [scrx_addr hL (by omega_arith), Offset.add_add, Nat.add_assoc]) hsep h4
      (by omega_arith) hs hdi hr fun j hj => by rw [Offset.add_add]; exact hc.inScrW (by omega_arith))
    fun u' ⟨hrd, hwr, hg, hf, hb⟩ hsy =>
    ⟨hc.keep (hsy := hsy) hL hrd hwr (hg _ (by decide)) hf
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega_arith)), hg, hf, hb⟩

/-- The pointers: `scratch` in `edi`, `d` in `esi`. -/
theorem ptrs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block msgPtrs) t fun u => Ctx L g m₀ u ∧ u.mem = t.mem ∧ u.gpr .edi = L.a3 ∧ u.gpr .esi = L.a1 := by
  rw [msgPtrs, show ([.mov .edi (argM 4), .mov .esi (argM 1)] : List Instr) =
    [.mov .edi (argM 4)] ++ [.mov .esi (argM 1)] from rfl, WP.block_append_iff]
  refine WP.mono (arg_ok hL hc (d := .edi) (by decide) (i := 4) (by omega_arith)) fun u₁ h₁ => ?_
  refine WP.mono (arg_ok hL h₁.ctx (d := .esi) (by decide) (i := 1) (by omega_arith)) fun u₂ h₂ =>
    ⟨h₂.ctx, by rw [h₂.mem, h₁.mem], by rw [h₂.keep _ (by decide), h₁.val]; rfl, h₂.val⟩

/-- `V`'s 64 bytes to `scratch + 2256`, then `scratch + D` in `edi`. -/
theorem msgV_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .edi = L.a3) :
    WP isa (.block msgV) t fun u => Ctx L g m₀ u ∧ (∀ r, r ≠ .eax → r ≠ .edi → u.gpr r = t.gpr r) ∧
      u.gpr .edi = L.a3 + BitVec.ofNat 32 dn ∧ Frame [⟨L.scr + BitVec.ofNat 64 2256, 64⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 2256) 64 =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 140) 64 := by
  have nc := hL.nc
  rw [msgV, WP.block_append_iff]
  refine WP.mono (copy_ok hL hc (S := L.F) (SA := L.B + BitVec.ofNat 64 140) (src := .esp) hc.esp (by decide)
    (x := 0) (by rw [hdi, BitVec.add_zero]) (so := 64) (d := 2256) (K := 16) (by omega_arith)
    (fun j hj => fr_addr hL (by omega_arith))
    (fun j hj => by rw [Offset.add_add]; exact hc.inFr (by omega_arith) (by omega_arith) hL)
    (hL.stk_scr (by omega_arith) (by omega_arith))) fun u₂ ⟨hc₂, hrd₂, hwr₂, hg₂, hf₂, hb₂⟩ => ?_
  have hdi₂ : u₂.gpr .edi = L.a3 := (hg₂ _ (by decide)).trans hdi
  refine wp_addS (hc₂.readPrm hL (i := 0) (by decide) rfl) fun u₃ v₃ _ => WP.block_nil ?_
  have hc₃ : Ctx L g m₀ u₃ := hc₂.regs hL v₃.rd v₃.wr v₃.mem (v₃.other _ (by decide)) v₃.syms
  refine ⟨hc₃, fun r h₁ h₂ => by rw [v₃.other _ h₂, hg₂ _ h₁], by rw [v₃.gpr, hdi₂]; rfl, ?_, ?_⟩
  · rw [v₃.mem]; simpa using hf₂
  · rw [v₃.mem]; simpa using hb₂

/-- `b`, then, if `full`, `‖ d ‖ h` (`Q` bytes each, `h` in the frame at
`B + 272`), at `scratch + D + 2256`, with `scratch + D` in `edi` and `d` in `esi`. -/
theorem msgTail_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (hdi : t.gpr .edi = L.a3 + BitVec.ofNat 32 dn)
    (hsi : t.gpr .esi = L.a1) (b : Nat) (full : Bool) {Q : Nat} (hD : dn ≤ 64) (h4 : 4 ≤ Q) (hQ : Q ≤ 68)
    (hq : Q ≤ L.q) :
    WP isa (.block (msgTail Q b full)) t fun u => Ctx L g m₀ u ∧
      Frame [⟨L.scr + BitVec.ofNat 64 (dn + 2256), 1 + 2 * Q⟩] t.mem u.mem ∧
      Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 (dn + 2256)) (if full then 1 + 2 * Q else 1) =
        [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d Q ++ Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 272) Q
            else []) := by
  have nc := hL.nc
  have nd := hL.nd
  have ea : addr (L.a3 + BitVec.ofNat 32 dn) sMsg = L.scr + BitVec.ofNat 64 (dn + 2256) :=
    scrx_addr hL (by simp only [sMsg]; omega_arith)
  rw [msgTail, WP.block_append_iff]
  refine wp_movi fun u₁ v₁ => wp_store8 (a := L.scr + BitVec.ofNat 64 (dn + 2256))
    (by show addr (u₁.gpr .edi) sMsg = _; rw [v₁.other .edi (by decide), hdi, ea])
    (by rw [v₁.wr]; exact hc.inScrW (o := dn + 2256) (n := 1) (by omega_arith)) fun u₂ v₂ => WP.block_nil ?_
  have hb8 : (u₁.gpr Reg8.al.reg).setWidth 8 = BitVec.ofNat 8 b := by
    rw [show Reg8.al.reg = .eax from rfl, v₁.gpr]
    apply BitVec.eq_of_toNat_eq; simp
  rw [hb8] at v₂
  have hm₂ : u₂.mem = t.mem.writeW (L.scr + BitVec.ofNat 64 (dn + 2256)) (BitVec.ofNat 8 b) := by
    rw [v₂.mem, v₁.mem]
  have hf₂ : Frame [⟨L.scr + BitVec.ofNat 64 (dn + 2256), 1⟩] t.mem u₂.mem := by
    rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hc₂ : Ctx L g m₀ u₂ := hc.keep (hsy := by rw [v₂.syms, v₁.syms]) hL (by rw [v₂.rd, v₁.rd])
    (by rw [v₂.wr, v₁.wr]) (by rw [v₂.gpr, v₁.other _ (by decide)]) hf₂
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_scr L (by omega_arith))
  have hbyte : Spec.Sha256.bytesAt u₂.mem (L.scr + BitVec.ofNat 64 (dn + 2256)) 1 = [BitVec.ofNat 8 b] := by
    show [u₂.mem (L.scr + BitVec.ofNat 64 (dn + 2256) + BitVec.ofNat 64 0)] = _
    rw [BitVec.add_zero, hm₂, WriteBytes.writeW8_apply]; simp
  have hg₂ : ∀ r, r ≠ .eax → u₂.gpr r = t.gpr r := fun r hr => by rw [v₂.gpr, v₁.other _ hr]
  cases full
  · simp only [Bool.false_eq_true, ite_false, List.append_nil]
    exact WP.block_nil ⟨hc₂, hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)⟩, hbyte⟩
  · simp only [ite_true]
    rw [WP.block_append_iff]
    refine WP.mono (copyB_ok hL hc₂ (src := .esi) (SA := L.d) (by rw [hg₂ _ (by decide), hsi]) (by decide)
      (x := dn) (by rw [hg₂ _ (by decide), hdi]) (so := 0) (d := sMsg + 1) h4 (by simp only [sMsg]; omega_arith)
      (fun j hj => by rw [Nat.zero_add]; exact addr_eq (by omega_arith))
      (fun j hj => hc₂.inD (by omega_arith) (by omega_arith))
      ((hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by simp only [sMsg]; omega_arith))))
      fun u₃ ⟨hc₃, hg₃, hf₃, hb₃⟩ => ?_
    refine WP.mono (copyB_ok hL hc₃ (src := .esp) (S := L.F) (SA := L.B + BitVec.ofNat 64 272) hc₃.esp (by decide)
      (x := dn) (by rw [hg₃ _ (by decide), hg₂ _ (by decide), hdi]) (so := fH) (d := sMsg + 1 + Q) h4
      (by simp only [sMsg]; omega_arith)
      (fun j hj => by rw [hL.addrF (by simp only [fH]; omega_arith), Offset.add_add]; simp only [fH]; congr 2; omega_arith)
      (fun j hj => by rw [Offset.add_add]; exact hc₃.inFr (by omega_arith) (by omega_arith) hL)
      (hL.stk_scr (by omega_arith) (by simp only [sMsg]; omega_arith))) fun u₄ ⟨hc₄, _, hf₄, hb₄⟩ => ?_
    simp only [sMsg] at hf₃ hb₃ hf₄ hb₄
    refine ⟨hc₄, ?_, ?_⟩
    · refine ((hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (hf₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).trans
        (hf₄.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
      all_goals simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · rw [show 1 + 2 * Q = 1 + (Q + Q) by omega_arith, Proof.Hmac.Common.bytesAt_add,
        Proof.Hmac.Common.bytesAt_add _ _ Q Q, Offset.add_add, Offset.add_add,
        show dn + 2256 + 1 = dn + (2256 + 1) by omega_arith, show dn + (2256 + 1) + Q = dn + (2256 + 1 + Q) by omega_arith,
        hb₄]
      have d₄ : Spec.Sha256.bytesAt u₄.mem (L.scr + BitVec.ofNat 64 (dn + (2256 + 1))) Q =
          Spec.Sha256.bytesAt u₃.mem (L.scr + BitVec.ofNat 64 (dn + (2256 + 1))) Q :=
        bytesAt_frame hf₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)
      have b₄ : Spec.Sha256.bytesAt u₄.mem (L.scr + BitVec.ofNat 64 (dn + 2256)) 1 = [BitVec.ofNat 8 b] := by
        rw [bytesAt_frame hf₄ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith),
          bytesAt_frame hf₃ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith), hbyte]
      have dd : Spec.Sha256.bytesAt u₂.mem L.d Q = Spec.Sha256.bytesAt t.mem L.d Q :=
        bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega_arith))) (by omega_arith)
      have hh : Spec.Sha256.bytesAt u₃.mem (L.B + BitVec.ofNat 64 272) Q =
          Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 272) Q := by
        rw [bytesAt_frame hf₃ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact hL.stk_scr (by omega_arith) (by omega_arith)) (by omega_arith),
          bytesAt_frame hf₂ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact hL.stk_scr (by omega_arith) (by omega_arith)) (by omega_arith)]
      rw [d₄, b₄, hb₃, dd, hh]

/-- The message `V ‖ b` (`‖ d ‖ h` if `full`, `Q` bytes each, `h` in the
frame at `B + 272`) at `scratch + 2256`, for `V` of `dn` bytes. -/
theorem msg_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (b : Nat) (full : Bool) {Q : Nat}
    (hD : dn ≤ 64) (h4 : 4 ≤ Q) (hQ : Q ≤ 66) (hq : Q ≤ L.q) :
    WP isa (.seq (.block msgPtrs) (.seq (.block msgV) (.block (msgTail Q b full)))) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.scr + BitVec.ofNat 64 2256, 200⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.scr + BitVec.ofNat 64 2256) (if full then dn + 2 * Q + 1 else dn + 1) =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 140) dn ++ [BitVec.ofNat 8 b] ++
          (if full then Spec.Sha256.bytesAt t.mem L.d Q ++ Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 272) Q
            else []) := by
  have nc := hL.nc
  refine WP.seq (WP.mono (ptrs_ok hL hc) fun p ⟨hcp, hmp, hdip, hsip⟩ => ?_)
  refine WP.seq (WP.mono (msgV_ok hL hcp hdip) fun u ⟨hcu, hgu, hdiu, hfu, hbu⟩ => ?_)
  refine WP.mono (msgTail_ok hL hcu hdiu (by rw [hgu _ (by decide) (by decide), hsip]) b full hD h4 (by omega_arith) hq)
    fun t' ⟨hc', hf', hb'⟩ => ⟨hc', ?_, ?_⟩
  · rw [← hmp]
    refine (hfu.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (hf'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    all_goals simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub _ (by omega_arith) (by omega_arith)
  · have e : (if full then dn + 2 * Q + 1 else dn + 1) = dn + (if full then 1 + 2 * Q else 1) := by
      cases full <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega_arith
    rw [e, Proof.Hmac.Common.bytesAt_add, Offset.add_add, show 2256 + dn = dn + 2256 by omega_arith, hb']
    have hv : Spec.Sha256.bytesAt t'.mem (L.scr + BitVec.ofNat 64 2256) dn =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 140) dn := by
      rw [bytesAt_frame hf' (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith),
        bytesAt_take _ _ (k := 64) hD, hbu, ← bytesAt_take _ _ hD, hmp]
    have hdq : Spec.Sha256.bytesAt u.mem L.d Q = Spec.Sha256.bytesAt t.mem L.d Q := by
      rw [bytesAt_frame hfu (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact (hL.dc.sub_left (Region.sub_prefix hq)).sub_right (Offset.sub_base _ (by omega_arith))) (by omega_arith), hmp]
    have hhq : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 272) Q =
        Spec.Sha256.bytesAt t.mem (L.B + BitVec.ofNat 64 272) Q := by
      rw [bytesAt_frame hfu (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hL.stk_scr (by omega_arith) (by omega_arith)) (by omega_arith), hmp]
    rw [hv, hdq, hhq, List.append_assoc]

end VG.Proof.Ecdsa.Rfc6979.X86
