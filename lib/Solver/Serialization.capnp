@0xd90b4ccaa01ea2f1;

using Cxx = import "/capnp/c++.capnp";
$Cxx.namespace("klee::serialization");

struct Query {
	constraints @0 :List(UInt32);
	expression @1 :UInt32;
	union {
		satUnsat @2 :Void;
		counterExArrayIds @3 :List(UInt32);
	}
	data :group{
		exprList @4 :List(Expr);
		arrayList @5 :List(Array);
		updateNodeList @6 :List(UpdateNode);
	}
}

struct Reply {
	union {
		unsolvable @0 :Void;
		sat :group{
			union{
				noAssignment @1 :Void;
				assignments @2 :List(List(UInt8));
			}
		}		
		unsat @3 :Void;
	}
}

struct Expr{
    enum Kind {
        constant @0;
        notOptimized @1;
        read @2;
        select @3;
        concat @4;
        extract @5;
        zExt @6;
        sExt @7;
        add @8;
        sub @9;
        mul @10;
        uDiv @11;
        sDiv @12;
        uRem @13;
        sRem @14;
        not @15;
        and @16;
        or @17;
        xor @18;
        shl @19;
        lShr @20;
        aShr @21;
        eq @22;
        ne @23;
        ult @24;
        ule @25;
        ugt @26;
        uge @27;
        slt @28;
        sle @29;
        sgt @30;
        sge @31;
        unknown @32;
    }
    
    kind @0 :Kind;
    width @1 :UInt32;
    
    union{
	    constantExpr :union{
	    	word @2 :UInt64;
	    	words @3 :List(UInt64);
	    }
	    nonConstantExpr :group{
		    kidIds @4 :List(UInt32);
		    union{
		        otherNonConst @5 :Void;
		        readExpr :group{
		            updateList @6 :UpdateList;
		        }
		        extractExpr :group{
		            offset @7 :UInt32;
		        }
		    }
	    }
    }
}

struct Array{
    name @0 :Text;
    size @1 :UInt32;
    domain @2 :UInt32;
    range @3 :UInt32;
    union{
    	symbolic @4 :Void;
	    constantIds @5 :List(UInt32);
    }
}

struct UpdateList{
    array @0 :UInt32;
    headNodeId @1 :UInt32;
}

struct UpdateNode{
    size @0 :UInt32;
    nextNodeId @1 :UInt32;
    indexExprId @2 :UInt32;
    valueExprId @3 :UInt32;
}
