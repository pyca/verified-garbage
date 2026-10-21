module

public import VerifiedGarbage.Proof.Weierstrass.Arm.TCombTable
public import VerifiedGarbage.Impl.Weierstrass.Arm.TComb
public import VerifiedGarbage.Proof.Mont.Arm.Words
import VerifiedGarbage.Proof.Weierstrass.Arm.TCombSelect
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-! Connect the ARM scan to the shared, kernel-checked comb tables. -/

@[expose] public section
namespace VG.Proof.Weierstrass.Arm.TComb
open VG VG.Arm VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.X25519.Arm

theorem selectTable_ok (K : TCombCfg) {s : State} {base T : Addr} {size a j R p : Nat}
    {tbl : List (List (Nat × Nat))}
    (hs : Scr s base size) (hq : K.Q.x+24*K.L.M.n≤size)
    (hzle : K.zero+8*K.L.M.n≤size)
    (hza : K.zero+8*K.L.M.n≤K.Q.x ∨ K.Q.x+24*K.L.M.n≤K.zero)
    (hone : K.one<2^(64*K.L.M.n)) (hz : wordsVal s.mem base K.zero K.L.M.n=0)
    (hn : 1≤K.L.M.n) (hH : K.H+1<2^31) (ha : a≤K.H)
    (ga : s.gpr .r9=BitVec.ofNat 32 a) (gj : s.gpr .r11=BitVec.ofNat 32 j)
    (hT : TableMem s T (tcombWords K.L.M.n R p tbl)) (sym : State.addr (s.syms K.tsym)=T)
    (hJ : tbl.length=K.J) (hRows : ∀ j<K.J,(tbl.getD j []).length=K.H) (hj : j<K.J)
    (hp : 0<p) (hpfit : p≤2^(64*K.L.M.n))
    (hd : Region.Disjoint ⟨T,8*(tcombWords K.L.M.n R p tbl).length⟩ ⟨base,size⟩)
    (er : encodable (BitVec.ofNat 32 (16*K.L.M.n*K.H))=true)
    (es : encodable (BitVec.ofNat 32 (16*K.L.M.n))=true)
    (eh : encodable (BitVec.ofNat 32 (K.H+1))=true) :
    WP isa K.select s fun t =>
      wordsVal t.mem base K.Q.x K.L.M.n=
        (if a=0 then 0 else (combAt tbl j (a-1)).1*R%p) ∧
      wordsVal t.mem base K.Q.y K.L.M.n=
        (if a=0 then K.one else (combAt tbl j (a-1)).2*R%p) ∧
      wordsVal t.mem base K.Q.z K.L.M.n=(if a=0 then 0 else K.one) ∧
      Rest [.r4,.r5,.r7,.r8,.r10] s t ∧ Outside base K.Q.x (24*K.L.M.n) s.mem t.mem := by
  have total := table_bytes (n := K.L.M.n) (R := R) (p := p) hJ hRows
  let X := off T (16*K.L.M.n*K.H*j)
  have row := hT.row total hj hd
  change X.toNat+16*K.L.M.n*K.H≤2^32 ∧
    InRegions (s.rd ++ s.wr) X (16*K.L.M.n*K.H) ∧
    Region.Disjoint ⟨X,16*K.L.M.n*K.H⟩ ⟨base,size⟩ at row
  have hHp : 1≤K.H := Nat.two_pow_pos _
  have span : 16*K.L.M.n*K.H*j+16*K.L.M.n*K.H≤8*(tcombWords K.L.M.n R p tbl).length := by
    rw [total,← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ hj
  have pos : 0<16*K.L.M.n*K.H := Nat.mul_pos (by omega) hHp
  have ptr : State.addr (s.syms K.tsym+BitVec.ofNat 32 (16*K.L.M.n*K.H*j))=X := by
    have fit := hT.fit
    have sn : (s.syms K.tsym).toNat=T.toNat := by rw [← sym,addr_toNat]
    rw [VG.Arm.addr_add (by rw [sn]; omega),sym]
  have entry := hT.entry hJ hRows hj (show a-1<K.H by omega)
    (Nat.lt_of_lt_of_le (Nat.mod_lt _ hp) hpfit) (Nat.lt_of_lt_of_le (Nat.mod_lt _ hp) hpfit)
  rw [Nat.mul_comm j (16*K.L.M.n*K.H)] at entry
  change wordsVal s.mem X (16*K.L.M.n*(a-1)) K.L.M.n=(combAt tbl j (a-1)).1*R%p ∧
    wordsVal s.mem X (16*K.L.M.n*(a-1)+8*K.L.M.n) K.L.M.n=(combAt tbl j (a-1)).2*R%p at entry
  refine WP.mono (selectRow_ok K hs hq hzle hza hone hz hn hH ha ga gj ptr
    row.1 row.2.1 row.2.2 er es eh) fun t ⟨x,y,z,keep,unch⟩ => ?_
  exact ⟨by rw [x,entry.1],by rw [y,entry.2],z,keep,unch⟩

end VG.Proof.Weierstrass.Arm.TComb
