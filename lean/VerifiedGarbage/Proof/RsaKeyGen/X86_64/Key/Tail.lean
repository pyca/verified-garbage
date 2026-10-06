import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Main
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Key.Contract

/-!
# An RSA key from its primes on x86-64: the key

`keyPart`, once `d` is not too small or does not exist: `qInv`, `dP`, `dQ`,
`n`, the final mask, the stores and the exit (`keyPart_k`); and the zeros
and the status 2 otherwise (`zerosPart_k`).
-/

namespace VG.Proof.RsaKeyGen.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.RsaKeyGen.X86_64.Key
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64.Public (exit)

/-- The outputs, in the order of the stores. -/
def outsL (I : KIn) : List (Addr × Nat) :=
  [(I.pN, 2 * I.pl), (I.pD, 2 * I.pl), (I.pP, I.pl), (I.pQ, I.pl), (I.pDp, I.pl), (I.pDq, I.pl), (I.pQi, I.pl)]

/-- The stores. -/
def storeL (I : KIn) : List St :=
  [⟨aQt, kNo, kNl, I.pN, 2 * I.pl⟩, ⟨aDd, kDo, kNl, I.pD, 2 * I.pl⟩, ⟨aPa, kPp, kPl, I.pP, I.pl⟩,
    ⟨aQa, kQp, kPl, I.pQ, I.pl⟩, ⟨aX₁, kDp, kPl, I.pDp, I.pl⟩, ⟨aV, kDq, kPl, I.pDq, I.pl⟩,
    ⟨aX₂, kQi, kPl, I.pQi, I.pl⟩]

/-- The outputs: writable, outside the working space, apart. -/
structure KOuts (I : KIn) : Prop where
  wr : ∀ o ∈ outsL I, ∀ i < o.2, InRegions I.Wr (o.1 + BitVec.ofNat 64 i) 1
  sep : ∀ o ∈ outsL I, ∀ i < o.2, I.Z ≤ ofs I.B (o.1 + BitVec.ofNat 64 i)
  apart : (outsL I).Pairwise fun a b => Apart a.1 a.2 b.1 b.2

theorem storeL_outs (I : KIn) : (storeL I).map (fun e => (e.out, e.len)) = outsL I := rfl

theorem storeL_pairwise {I : KIn} (O : KOuts I) :
    (storeL I).Pairwise fun a b => Apart a.out a.len b.out b.len := by
  have := O.apart
  rw [← storeL_outs, List.pairwise_map] at this
  exact this

theorem st_ok {I : KIn} {m₀ : Mem} {t : State} (h : KS I m₀ t) (O : KOuts I) {j p l : Nat} {out : Addr}
    {len : Nat} (hj : j < 16) (hp : p < 32) (hl : l < 32) (hpv : word t.mem I.B (8 * p) = out)
    (hlv : word t.mem I.B (8 * l) = BitVec.ofNat 64 len) (hl1 : 1 ≤ len) (hlw : len ≤ 8 * I.W)
    (ho : (out, len) ∈ outsL I) : (⟨j, p, l, out, len⟩ : St).Ok t I.B I.Z I.W :=
  ⟨hj, hp, hl, hpv, hlv, hl1, hlw, fun i hi => by rw [h.wr]; exact O.wr _ ho i hi, O.sep _ ho⟩

theorem storeL_ok {I : KIn} {m₀ : Mem} {t : State} (h : KS I m₀ t) (L : KLens I) (O : KOuts I) :
    ∀ e ∈ storeL I, e.Ok t I.B I.Z I.W := by
  have hW := L.W
  have hpl := L.pl1
  have h8 := L.pl8
  intro e he
  simp only [storeL, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.no h.args.nl (by omega) (by omega) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.dd h.args.nl (by omega) (by omega) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.pp h.args.pl (by omega) (by omega) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.qp h.args.pl (by omega) (by omega) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.dp h.args.pl (by omega) (by omega) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.dq h.args.pl (by omega) (by omega) (by simp [outsL])
  · exact st_ok h O (by decide) (by decide) (by decide) h.args.qi h.args.pl (by omega) (by omega) (by simp [outsL])

theorem outputs_eq (I : KIn) : outputs = storesK (storeL I) ++
    ([.block (([.mov .rax (.mem (hdr kOk)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)] : List (Prog isa)) := rfl

theorem zeros_eq (I : KIn) (st : Nat) : zeros st = seqs (zerosK (storeL I) ++
    ([.block (([.mov32 .rax (.imm (BitVec.ofNat 32 st))] : List Instr) ++ exit)] : List (Prog isa))) := rfl

theorem keyPart_eq (I : KIn) : keyPart = seqs (qinvPart ++ (crtPart ++ (nPart ++ (([.block finalMask] : List (Prog isa)) ++
    (storesK (storeL I) ++ ([.block (([.mov .rax (.mem (hdr kOk)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)] : List (Prog isa))))))) := by
  rw [keyPart, ← outputs_eq I]; simp only [List.append_assoc]

/-- A number below `2^(64 v)` read from `v ≤ W` words. -/
theorem wv_of_av {I : KIn} {m : Mem} {j v x : Nat} (hv : v ≤ I.W) (h : av I m j = x) (hx : x < 2 ^ (64 * v)) :
    wv m I.B (slot I.W j) v = x := by
  rw [← h]; exact wv_low_of_lt hv (by rw [show wv m I.B (slot I.W j) I.W = av I m j from rfl, h]; exact hx)

/-- What `keyPart` leaves, from `Front` and `kOk` the mask of `ok`. -/
def TailPost (I : KIn) (s t : State) (ok : Bool) : Prop :=
  ∃ x : Nat, ((qMod I.P : Nat) : Int) ∣ (x : Int) * I.Q - Nat.gcd I.Q (qMod I.P) ∧ x < qMod I.P ∧
    (let c := finalOk I.W (I.P * I.Q) I.P I.Q I.E (decide (Nat.gcd I.Q (qMod I.P) = 1) && ok)
     t.gpr .rax = BitVec.ofNat 64 c.toNat ∧
     Spec.Rsa.bytesAt t.mem I.pN (2 * I.pl) = Spec.Rsa.i2osp (if c then I.P * I.Q else 0) (2 * I.pl) ∧
     Spec.Rsa.bytesAt t.mem I.pD (2 * I.pl) = Spec.Rsa.i2osp (if c then av I s.mem aDd else 0) (2 * I.pl) ∧
     Spec.Rsa.bytesAt t.mem I.pP I.pl = Spec.Rsa.i2osp (if c then I.P else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pQ I.pl = Spec.Rsa.i2osp (if c then I.Q else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pDp I.pl = Spec.Rsa.i2osp (if c then av I s.mem aDd % dv (I.P - 1) else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pDq I.pl = Spec.Rsa.i2osp (if c then av I s.mem aDd % dv (I.Q - 1) else 0) I.pl ∧
     Spec.Rsa.bytesAt t.mem I.pQi I.pl = Spec.Rsa.i2osp (if c then x else 0) I.pl) ∧
    (∀ i < 6, t.gpr (saved.getD i .rax) = I.sv i) ∧
    (∀ y, I.Z ≤ ofs I.B y → (∀ o ∈ outsL I, ∀ i < o.2, y ≠ o.1 + BitVec.ofNat 64 i) → t.mem y = s.mem y) ∧
    t.gpr .rsp = I.sp

/-- `keyPart`. -/
theorem keyPart_k {I : KIn} {m₀ : Mem} {s : State} (h : Front I m₀ s) (L : KLens I) (O : KOuts I) {ok : Bool}
    (hok : word s.mem I.B (8 * kOk) = mask ok) :
    WP isa keyPart s (fun t => TailPost I s t ok) := by
  have hk := h.ks
  have hZ := hk.hZ
  have hW := L.W
  have hw8 : 8 * I.pl = 64 * (I.pl / 8) := by have := L.pl8; omega
  have hPw : I.P < 2 ^ (64 * (I.pl / 8)) := by
    have := lt_of_os2ip_len L.pbl; have := lt_of_os2ip_len L.qbl
    simp only [KIn.P, KIn.P₀, KIn.Q₀]; rw [← hw8]; split <;> omega
  have hQw : I.Q < 2 ^ (64 * (I.pl / 8)) := by
    have := lt_of_os2ip_len L.pbl; have := lt_of_os2ip_len L.qbl
    simp only [KIn.Q, KIn.P₀, KIn.Q₀]; rw [← hw8]; split <;> omega
  rw [keyPart_eq I]
  -- `qInv`.
  refine wp_seqs_append (by simp [qinvPart]) (by simp [crtPart, divisorOf]) (WP.mono (qinvPart_k hk h.vP h.vQ hok)
    fun s₁ ⟨h₁, f₁, ok₁, hdv₁, hx₁⟩ => ?_)
  generalize hx : av I s₁.mem aX₂ = x at hdv₁ hx₁
  have hokQ : csQ.all Rc.ok = true := by decide
  -- `dP`, `dQ`.
  refine wp_seqs_append (by simp [crtPart, divisorOf]) (by simp [nPart]) (WP.mono (crtPart_k h₁
    (d := av I s.mem aDd) (a := I.P - 1) (b := I.Q - 1) (by rw [f₁.av hokQ (by decide) (by decide) hZ])
    (by rw [f₁.av hokQ (by decide) (by decide) hZ, h.vPm]) (by rw [f₁.av hokQ (by decide) (by decide) hZ, h.vQm]))
    fun s₂ ⟨h₂, f₂, dP₂, dQ₂⟩ => ?_)
  have hokC : csC.all Rc.ok = true := by decide
  -- `n`.
  refine wp_seqs_append (by simp [nPart]) (by simp) (WP.mono (nPart_k h₂ hW
    (by rw [f₂.av hokC (by decide) (by decide) hZ, f₁.av hokQ (by decide) (by decide) hZ]; exact h.vP)
    (by rw [f₂.av hokC (by decide) (by decide) hZ, f₁.av hokQ (by decide) (by decide) hZ]; exact h.vQ) hPw hQw)
    fun s₃ ⟨h₃, f₃, n₃⟩ => ?_)
  have hn : I.P * I.Q < 2 ^ (64 * I.W) := by
    rw [hW, show 64 * (2 * (I.pl / 8)) = 64 * (I.pl / 8) + 64 * (I.pl / 8) by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le hPw (by omega) (Nat.two_pow_pos _)
  have hokN : [Rc.arr aQt].all Rc.ok = true := by decide
  have vN₃ : av I s₃.mem aQt = I.P * I.Q := av_of_full n₃ hn
  have vP₃ : av I s₃.mem aPa = I.P := by
    rw [f₃.av hokN (by decide) (by decide) hZ, f₂.av hokC (by decide) (by decide) hZ,
      f₁.av hokQ (by decide) (by decide) hZ, h.vP]
  have vQ₃ : av I s₃.mem aQa = I.Q := by
    rw [f₃.av hokN (by decide) (by decide) hZ, f₂.av hokC (by decide) (by decide) hZ,
      f₁.av hokQ (by decide) (by decide) hZ, h.vQ]
  have ev₃ : word s₃.mem I.B (8 * kEv) = BitVec.ofNat 64 I.E := by
    rw [f₃.word hokN (by decide) (by decide), f₂.word hokC (by decide) (by decide),
      f₁.word hokQ (by decide) (by decide), h.ev]
  have ok₃ : word s₃.mem I.B (8 * kOk) = mask (decide (Nat.gcd I.Q (qMod I.P) = 1) && ok) := by
    rw [f₃.word hokN (by decide) (by decide), f₂.word hokC (by decide) (by decide), ok₁]
  have hE : I.E < 2 ^ 64 := by
    have := lt_of_os2ip_len L.ebl
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by have := L.el8; omega))
  -- The final mask.
  refine wp_seqs_append (by simp) (by simp [storesK, storeL, storeA]) ?_
  simp only [seqs]
  refine WP.mono (finalMask_k h₃ vN₃ vP₃ vQ₃ hE ev₃ ok₃) fun s₄ ⟨h₄, f₄, ok₄⟩ => ?_
  generalize hc : finalOk I.W (I.P * I.Q) I.P I.Q I.E (decide (Nat.gcd I.Q (qMod I.P) = 1) && ok) = cv at ok₄
  have hokO : [Rc.hdr kOk].all Rc.ok = true := by decide
  have v4 : ∀ j, j < 16 → Rc.arr j ∉ [Rc.arr aQt] → Rc.arr j ∉ csC → Rc.arr j ∉ csQ →
      av I s₄.mem j = av I s.mem j := fun j hj h1 h2 h3 => by
    rw [f₄.av hokO hj (by simp) hZ, f₃.av hokN hj h1 hZ, f₂.av hokC hj h2 hZ, f₁.av hokQ hj h3 hZ]
  -- The stores and the exit.
  refine stores_ok (Q := fun t => TailPost I s t ok) (storeL I) _ s₄ (by simp) h₄.ws ok₄ (storeL_ok h₄ L O)
    (storeL_pairwise O) fun t ht ft bt xt kt => ?_
  simp only [seqs]
  refine WP.mono (keyExit_ok ht (c := cv) (by rw [frm_word ft ht.h256 (by decide)]; exact ok₄))
    fun u ⟨hax, hsv, hmu, ku⟩ => ?_
  have b := fun e he => (bt e he)
  simp only [storeL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at b
  obtain ⟨bN, bD, bP, bQ, bDp, bDq, bQi⟩ := b
  have hlen : (I.pl + 7) / 8 = I.pl / 8 := by have := L.pl8; omega
  have hlen2 : (2 * I.pl + 7) / 8 = I.W := by have := L.pl8; simp only [KIn.W]; omega
  have hv : I.pl / 8 ≤ I.W := by omega
  have hdvw : ∀ a, a ≤ I.P → dv a < 2 ^ (64 * (I.pl / 8)) := fun a ha => by
    unfold dv; split
    · exact Nat.one_lt_two_pow (by have := L.pl1; omega)
    · omega
  have hdvwq : ∀ a, a ≤ I.Q → dv a < 2 ^ (64 * (I.pl / 8)) := fun a ha => by
    unfold dv; split
    · exact Nat.one_lt_two_pow (by have := L.pl1; omega)
    · omega
  have hdv0 : ∀ a, 0 < dv a := fun a => by unfold dv; split <;> omega
  have hqm : qMod I.P < 2 ^ (64 * (I.pl / 8)) := by
    unfold qMod; split
    · exact hPw
    · exact Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (by decide) (show 2 ≤ 64 * (I.pl / 8) by
        have := L.pl1; omega))
  have iv : ∀ {len v : Nat} {o : Addr} {w' : Nat},
      (List.range len).map (fun i => t.mem (o + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if cv then w' else 0) len → w' = v →
      Spec.Rsa.bytesAt u.mem o len = Spec.Rsa.i2osp (if cv = true then v else 0) len := fun hb hw => by
    simp only [Spec.Rsa.bytesAt]; rw [hmu, hb, hw]
  refine ⟨x, hdv₁, hx₁, ?_, fun i hi => ?_, fun y hy hny => ?_, ?_⟩
  · dsimp only
    rw [hc]
    refine ⟨hax, iv bN ?_, iv bD ?_, iv bP ?_, iv bQ ?_, iv bDp ?_, iv bDq ?_, iv bQi ?_⟩
    · rw [hlen2]; show av I s₄.mem aQt = _; rw [f₄.av hokO (by decide) (by decide) hZ, vN₃]
    · rw [hlen2]; exact v4 aDd (by decide) (by decide) (by decide) (by decide)
    · rw [hlen]; exact wv_of_av hv (v4 aPa (by decide) (by decide) (by decide) (by decide) |>.trans h.vP) hPw
    · rw [hlen]; exact wv_of_av hv (v4 aQa (by decide) (by decide) (by decide) (by decide) |>.trans h.vQ) hQw
    · rw [hlen]
      refine wv_of_av hv (by rw [f₄.av hokO (by decide) (by decide) hZ, f₃.av hokN (by decide) (by decide) hZ, dP₂])
        (Nat.lt_of_lt_of_le (Nat.mod_lt _ (hdv0 _)) (Nat.le_of_lt (hdvw _ (by omega))))
    · rw [hlen]
      refine wv_of_av hv (by rw [f₄.av hokO (by decide) (by decide) hZ, f₃.av hokN (by decide) (by decide) hZ, dQ₂])
        (Nat.lt_of_lt_of_le (Nat.mod_lt _ (hdv0 _)) (Nat.le_of_lt (hdvwq _ (by omega))))
    · rw [hlen]
      refine wv_of_av hv (by rw [f₄.av hokO (by decide) (by decide) hZ, f₃.av hokN (by decide) (by decide) hZ,
        f₂.av hokC (by decide) (by decide) hZ, hx]) (by omega)
  · rw [hsv i hi, frm_word ft ht.h256 (by omega)]; exact h₄.args.saved i hi
  · have hy' : ∀ e ∈ storeL I, ∀ i < e.len, y ≠ e.out + BitVec.ofNat 64 i := fun e he i hi =>
      hny (e.out, e.len) (by rw [← storeL_outs]; exact List.mem_map_of_mem he) i hi
    rw [hmu, xt y hy', h₄.inScr y hy, hk.inScr y hy]
  · rw [ku.gpr (by decide), kt.gpr (by decide), h₄.rsp]

/-- The status `st` returned and the saved registers restored. -/
theorem stExit_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) (st : Nat) :
    WP isa (.block (([.mov32 .rax (.imm (BitVec.ofNat 32 st))] : List Instr) ++ exit)) s
      fun t => t.gpr .rax = (BitVec.ofNat 32 st).setWidth 64 ∧
        (∀ i < 6, t.gpr (saved.getD i .rax) = word s.mem B (8 * i)) ∧
        t.mem = s.mem ∧ Keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hs.ld (by omega)
  rw [exit_eq]
  refine WP.mono (WP.keep [.rax, .rbx, .rbp, .r12, .r13, .r14, .r15] (Q := fun t =>
      t.gpr .rax = (BitVec.ofNat 32 st).setWidth 64 ∧ t.gpr .rbx = word s.mem B (8 * 0) ∧
      t.gpr .rbp = word s.mem B (8 * 1) ∧ t.gpr .r12 = word s.mem B (8 * 2) ∧
      t.gpr .r13 = word s.mem B (8 * 3) ∧ t.gpr .r14 = word s.mem B (8 * 4) ∧
      t.gpr .r15 = word s.mem B (8 * 5) ∧ t.mem = s.mem) (by
    simp only [List.cons_append, List.nil_append]
    xrun [State.ea, hdr, h.rdi, hdrOff, hl 0 (by decide), hl 1 (by decide), hl 2 (by decide), hl 3 (by decide),
      hl 4 (by decide), hl 5 (by decide)]) rfl)
    fun t ⟨⟨hax, h0, h1, h2, h3, h4, h5, hm'⟩, k⟩ => ⟨hax, ?_, hm', k⟩
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

/-- What `zeros 2` leaves. -/
def ZerosPost (I : KIn) (s t : State) : Prop :=
  t.gpr .rax = (BitVec.ofNat 32 2).setWidth 64 ∧
    (∀ o ∈ outsL I, Spec.Rsa.bytesAt t.mem o.1 o.2 = List.replicate o.2 0) ∧
    (∀ i < 6, t.gpr (saved.getD i .rax) = I.sv i) ∧
    (∀ y, I.Z ≤ ofs I.B y → (∀ o ∈ outsL I, ∀ i < o.2, y ≠ o.1 + BitVec.ofNat 64 i) → t.mem y = s.mem y) ∧
    t.gpr .rsp = I.sp

/-- `zeros 2`: zeros to the outputs, and the status 2. -/
theorem zerosPart_k {I : KIn} {m₀ : Mem} {s : State} (h : KS I m₀ s) (L : KLens I) (O : KOuts I) :
    WP isa (zeros 2) s (ZerosPost I s) := by
  rw [zeros_eq I]
  refine zeros_ok (storeL I) _ s (by simp) h.ws (storeL_ok h L O) (storeL_pairwise O)
    fun t ht ft zt xt kt => ?_
  simp only [seqs]
  refine WP.mono (stExit_ok ht 2) fun u ⟨hax, hsv, hmu, ku⟩ => ⟨hax, fun o ho => ?_, fun i hi => ?_,
    fun y hy hny => ?_, ?_⟩
  · rw [← storeL_outs] at ho
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
    refine List.eq_replicate_iff.mpr ⟨by simp [Spec.Rsa.bytesAt], fun b hb => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    rw [hmu]; exact zt e he i (List.mem_range.mp hi)
  · rw [hsv i hi, frm_word ft ht.h256 (by omega)]; exact h.args.saved i hi
  · have hy' : ∀ e ∈ storeL I, ∀ i < e.len, y ≠ e.out + BitVec.ofNat 64 i := fun e he i hi =>
      hny (e.out, e.len) (by rw [← storeL_outs]; exact List.mem_map_of_mem he) i hi
    rw [hmu, xt y hy']
  · rw [ku.gpr (by decide), kt.gpr (by decide), h.rsp]

end VG.Proof.RsaKeyGen.X86_64.Key
