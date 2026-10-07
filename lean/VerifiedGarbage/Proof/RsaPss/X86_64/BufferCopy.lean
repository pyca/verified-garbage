import VerifiedGarbage.Impl.RsaPss.X86_64.Buffers
import VerifiedGarbage.Proof.RsaPss.X86_64.Loops
import VerifiedGarbage.Proof.Pbkdf2.X86_64.Copy

/-! Word copies preserve exactly the same byte-level buffer contents. -/
namespace VG.Proof.RsaPss.X86_64
open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MdStream.X86_64 (wp_movm wp_store)
open VG.Proof.Pbkdf2.X86_64 (ea_off)
open VG.Proof.Hmac.Common (copy_mem bytesAt_zero)
open VG.WriteBytes (writeBytes writeBytes_nil)
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Bignum (off)

/-- `n` full words copied between disjoint buffers. -/
theorem copyWords64_ok {src dst : Reg} (hs : src ≠ .rax) (hd : dst ≠ .rax) (so doff n : Nat) :
    ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    (∀ k < n, InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 so + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ k < n, InRegions s.wr (s.gpr dst + BitVec.ofNat 64 doff + BitVec.ofNat 64 (8 * k)) 8) →
    Mem.Sep (s.gpr src + BitVec.ofNat 64 so) (8 * n) (s.gpr dst + BitVec.ofNat 64 doff) (8 * n) →
    8 * n < 2 ^ 64 →
    (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = writeBytes s.mem (s.gpr dst + BitVec.ofNat 64 doff)
        (bytesAt s.mem (s.gpr src + BitVec.ofNat 64 so) (8 * n)) → WP isa (.block rest) s' Q) →
    WP isa (.block (copyWords64 src dst so doff n ++ rest)) s Q := by
  induction n with
  | zero =>
    intro rest s Q _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by rw [Nat.mul_zero, bytesAt_zero, writeBytes_nil])
  | succ n ih =>
    intro rest s Q hin hout hsep hlt k
    unfold copyWords64
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih _ s Q (fun j hj => hin j (by omega)) (fun j hj => hout j (by omega))
      (fun x hx hy => hsep x (by omega) (by omega)) (by omega) fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [copyWord64, List.cons_append, List.nil_append]
    refine wp_movm (a := s.gpr src + BitVec.ofNat 64 so + BitVec.ofNat 64 (8 * n))
      (by rw [ea_off, g₁ _ hs]) (by rw [rd₁, wr₁]; exact hin n (by omega)) fun s₂ u₂ => ?_
    refine wp_store (a := s.gpr dst + BitVec.ofNat 64 doff + BitVec.ofNat 64 (8 * n))
      (by rw [ea_off, u₂.other _ hd, g₁ _ hd]) (by rw [u₂.wr, wr₁]; exact hout n (by omega))
      fun s₃ g₃ m₃ rd₃ wr₃ => k s₃ (fun r hr => by rw [g₃, u₂.other r hr, g₁ r hr])
        (by rw [rd₃, u₂.rd, rd₁]) (by rw [wr₃, u₂.wr, wr₁]) ?_
    rw [m₃, u₂.gpr, u₂.mem, m₁, Nat.mul_succ]
    exact copy_mem s.mem _ _ n 8 (by rwa [← Nat.mul_succ]) (by omega)

/-- The same copy, within PSS's working space, expressed in its byte view. -/
theorem copyScratchWords_ok {u : State} {F S : Addr} (L : Lay u F S)
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W)
    {src dst : Reg} (hs : src ≠ .rax) (hd : dst ≠ .rax) {a b n : Nat}
    (ha : a + 8 * n ≤ oRsa) (hb : b + 8 * n ≤ oRsa)
    (hsep : a + 8 * n ≤ b ∨ b + 8 * n ≤ a)
    (hsrc : u.gpr src = off S a) (hdst : u.gpr dst = off S b) :
    WP isa (.block (copyWords64 src dst 0 0 n)) u fun t =>
      Lay t F S ∧ Keep [.rax] u t ∧
      Rep t.mem F S (cpV V (fun i => V (a + i)) b (8 * n)) W := by
  rw [← List.append_nil (copyWords64 src dst 0 0 n)]
  refine copyWords64_ok hs hd 0 0 n [] u _ (fun k hk => ?_) (fun k hk => ?_) ?_
    (by unfold oRsa at ha; omega) fun t g rd wr hm => ?_
  · simp only [hsrc, BitVec.add_zero, off_plus]
    exact L.sld (by omega)
  · simp only [hdst, BitVec.add_zero, off_plus]
    exact L.sst (by omega)
  · simp only [hsrc, hdst, BitVec.add_zero]
    exact Offset.sep S hsep (by unfold oRsa at ha; omega) (by unfold oRsa at hb; omega)
  · simp only [hsrc, hdst, BitVec.add_zero] at hm
    have R' := R.wbs L.geo (xs := bytesAt u.mem (off S a) (8 * n)) (by simp [bytesAt]; exact hb)
    rw [← hm] at R'
    have R'' : Rep t.mem F S (cpV V (fun i => V (a + i)) b (8 * n)) W := by
      refine (congrArg (fun V' => Rep t.mem F S V' W) (funext fun x => ?_)).mp R'
      simp only [bytesAt, List.length_map, List.length_range, cpV]
      split
      · rename_i hx
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
        simp only [Option.map_some, Option.getD_some, off_plus]
        exact R.scr _ (by omega)
      · rfl
    have k : Keep [.rax] u t := ⟨fun r hr => g r (by simpa using hr), rd, wr⟩
    exact WP.block_nil ⟨L.of_rep R R'' (k.gpr (by decide)) wr, k, R''⟩

/-- Byte fallback for a fixed length that is not a whole number of words. -/
theorem copyScratchBytes_ok {u : State} {F S : Addr} (L : Lay u F S)
    {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep u.mem F S V W)
    {a b n : Nat} (hn : 0 < n) (ha : a + n ≤ oRsa) (hb : b + n ≤ oRsa)
    (hsep : a + n ≤ b ∨ b + n ≤ a)
    (hsrc : u.gpr .rsi = off S a) (hdst : u.gpr .rcx = off S b) :
    WP isa (.seq (.block [.mov32 .r8 (.imm 0)])
      (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rcx .r8) .rax]
        (.imm (BitVec.ofNat 32 n)))) u fun t =>
      Lay t F S ∧ Keep [.rax, .r8] u t ∧ Rep t.mem F S (cpV V (fun i => V (a + i)) b n) W := by
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r8] (Q := fun v =>
    v.gpr .r8 = BitVec.ofNat 64 0 ∧ v.mem = u.mem) ?_ rfl) fun v ⟨⟨h8, hm⟩, hk⟩ => ?_)
  · xrun []
  have Lv : Lay v F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  have Rv : Rep v.mem F S V W := hm ▸ R
  refine WP.mono (copy_ok Lv Rv (d := .rcx) (by decide) (p := off S a) (o := b) (disp := 0) (n := n)
    (stepI_ok (by unfold oRsa at ha; omega) v [.rax, .r8]) hn hb
    ((hk.gpr (by decide)).trans hsrc) ((hk.gpr (by decide)).trans hdst) h8
    (fun i hi => by rw [off_plus]; exact Lv.sld8 (by omega))
    (fun i hi j hj => by
      rw [off_plus]; exact Offset.add_ofNat_ne S (by unfold oRsa at ha; omega)
        (by unfold oRsa at hb; omega) (by omega))) fun t ⟨Lt, kt, Rt⟩ => ?_
  refine ⟨Lt, (hk.trans kt).mono (by decide), ?_⟩
  refine (congrArg (fun V' => Rep t.mem F S V' W) (funext fun x => ?_)).mp Rt
  simp only [cpV, Nat.add_zero]
  split
  · rw [off_plus, Rv.scr _ (by omega)]
  · rfl

end VG.Proof.RsaPss.X86_64
