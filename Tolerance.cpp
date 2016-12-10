#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Value.h"
using namespace llvm;

namespace {
  typedef std::map<Value*, Value*> VectorizeMapTable;
/**===================VectorizeMap========================**/
  class VectorizeMap {
    VectorizeMapTable vmap;

    public:
    VectorizeMap(): vmap() {}
    bool IsAdded(Value *sca) {
	return vmap.find(sca)!=vmap.end();
    }
    void AddPair(Value* sca, Value* vec) {
	VectorizeMapTable::iterator iter=vmap.find(sca);
        if(iter == vmap.end())//do not find vectorize
	  vmap.insert(std::make_pair(sca, vec));
        else
          errs()<<"Error:"<<*sca <<" has been vectorized.\n";
    }
    Value* GetVector(Value* sca) {
        VectorizeMapTable::iterator iter=vmap.find(sca);
        if(iter != vmap.end())//find vectorize
           return iter->second;
        else
           return NULL;
    }
    VectorizeMapTable::iterator GetBegin() {
        return vmap.begin();
    }
    VectorizeMapTable::iterator GetEnd() {
        return vmap.end();
    }
  };
  void PrintMap(VectorizeMap *map)
  {
        errs() <<"Show Vector Map:\n";
        VectorizeMapTable::iterator iter;
        for(iter = map->GetBegin();iter!=map->GetEnd();iter++){
            Value* v_sca=iter->first;
            Value* v_vec=iter->second;
            errs() << *v_sca << ": " << *v_vec << "\n";
        }
  }
  Value* GetVecOpValue(IRBuilder<> builder,Value* val,VectorizeMap vec_map){
	if(isa<LoadInst>(val)){//find add inst and 2 op is load, do SIMD "add"
        //errs()<< "****GetVecOpValue Load!\n";
		LoadInst* ld_inst = cast<LoadInst>(val);//value to loadinst
		Value* sca = ld_inst->getPointerOperand();
		//errs()<<"sca:"<<*sca<<"\n";
		Value *alloca_vec = vec_map.GetVector(sca);
		//errs()<<"get vector:"<<*alloca_vec<<"\n";
		//create load before "add"
		LoadInst* load_val=builder.CreateLoad(alloca_vec);
		load_val->setAlignment(16);
		return load_val;
	}else if(isa<BinaryOperator>(val)){
		//errs()<< "****GetVecOpValue BinaryOperator!\n";
        BinaryOperator* bin_inst=cast<BinaryOperator>(val);
        //errs()<<"bin_inst:"<<*bin_inst<<"\n";
        Value *bin_vec = vec_map.GetVector(bin_inst);
        //errs()<<"get vector:"<<*bin_vec<<"\n";
        return bin_vec;
	}else if(isa<Constant>(val)){
    	//ConstantInt* c_inst=cast<ConstantInt>(val);
		//errs()<< "****GetVecOpValue Constant!"<<*val <<"\n";
        //create sca alloca and vec alloca, store constant and load into insertelement.
        auto alloca_c = builder.CreateAlloca(val->getType());
        alloca_c->setAlignment(4);
        auto allocaVec = builder.CreateAlloca(VectorType::get(val->getType(), 4));
        //errs()<<"****constant:"<<val->getSplatValue () <<"\n";
        allocaVec->setAlignment(16);
        //errs()<<"****alloca_c:"<<*alloca_c<<"\n";
        auto store_c = builder.CreateStore(val,alloca_c);
        auto load_c = builder.CreateLoad(alloca_c);
        load_c->setAlignment(4);
        //errs()<<"****store_c:"<<*store_c<<"\n";
        //errs()<<"****load_c:"<<*load_c<<"\n";
        Type* load_ty= load_c->getType();
        //errs()<<"****load_ty:"<<*load_ty<<"\n";
        Value* val_c = UndefValue::get(VectorType::get(load_ty, 4));
        //Value *mul_value = ConstantInt::get(val->getType() , *val); 
        for (unsigned i = 0; i < 4; i++)//for 4 copies
        {
			val_c = builder.CreateInsertElement(val_c,load_c, builder.getInt32(i));  
        }
        //errs()<<"****val_c:"<<*val_c<<"\n";
        auto store_val=builder.CreateStore(val_c,allocaVec);
        store_val->setAlignment(4);
        auto load_val=builder.CreateLoad(allocaVec);
        load_val->setAlignment(4);
        return load_val;
        }
      return NULL;
  }
  void ReplaceUnsafe(StoreInst *from, StoreInst *to) {
  while (!from->use_empty()) {
    auto &U = *from->use_begin();
    U.set(to);
  }
    from->eraseFromParent();
  }

  struct TolerancePass : public FunctionPass {
    static char ID;
    TolerancePass() : FunctionPass(ID) {}
    
    virtual bool runOnFunction(Function &F) {
      errs() << "function name: " << F.getName() << "\n";

      //errs() << "Function body:\n";
      //F.dump();
      VectorizeMap vec_map;
      VectorizeMap check_map;
      BasicBlock::iterator ignoreuntilinst;
      for (auto &B : F) {
        //errs() << "Basic block:\n";
        //B.dump();
        bool BuilderAfterflag=1;
        for (auto &I : B) {
        //BasicBlock* bb=I.getParent();
        //Find allocation instruction
        if(BuilderAfterflag){
        if (auto *op = dyn_cast<AllocaInst>(&I)) {
            //errs()<< "Tolerance:Find AllocaInst!\n";
            
            IRBuilder<> builder(op);
            
            Type* scalar_t= op->getAllocatedType();//not pointer
            //Type* scalar_t1= op->getType();//pointer
            //errs()<<*scalar_t<<"\n";
            //errs()<<*scalar_t1<<"\n";
            //support inst type?
            if(scalar_t->isIntegerTy()){
                
                //errs()<<"Find integer:"<<*scalar_t<<"\n";
	        	auto allocaVec = builder.CreateAlloca(VectorType::get(scalar_t, 4));
                allocaVec->setAlignment(16);
                //errs()<<"address sca:"<<*op<<",vec:"<<*allocaVec<<"\n";
                vec_map.AddPair(op,allocaVec);
                //get vector demo
                auto *vec = vec_map.GetVector(op);
                errs()<< "Tolerance:Create AllocaInst Vectorty:"<<*vec<<"\n";
                //errs()<<"get vector:"<<*vec<<"\n";
            }  
            if(scalar_t->isFloatTy()){
                //errs()<<"Find float:"<<"*scalar_t"<<"\n";
                /*auto allocaVec = builder.CreateAlloca(VectorType::get(op->getType(), 4));
                allocaVec->setAlignment(4);*/
            }
            if(scalar_t->isVectorTy()){
                //errs()<<"Find vector:"<<*scalar_t<<"\n";
            }
        }

        else if (StoreInst *op = dyn_cast<StoreInst>(&I)) {
            //IRBuilder<> builder(op);
            //Value* store_v=op->getValueOperand();//value
	        //errs()<<"~Find store_v:"<<*store_v<<"\n";
	       
            //Value* store_p=op->getPointerOperand();//pointer
	        //errs()<<"~Find store_p:"<<*store_p<<"\n";
            //Type* load_ty= store_p->getType();
            //errs()<<"~Load type:"<<*load_ty<<"\n";
            
            
            //create store into original vector register
            //auto *map_vec = vec_map.GetVector(store_p);
            //Instruction to Value type
           /* Value* lhs = op->getOperand(0);
	    	Value* rhs = op->getOperand(1);
	    	errs()<<"~~get store:"<<*lhs<<"\n";
	    	errs()<<"~~get store1:"<<*rhs<<"\n";
            //checkpoint
	    	if(isa<BinaryOperator>(lhs)&&isa<AllocaInst>(rhs)) {//final store after binop
                //store final binaryop value into vector
	    		BinaryOperator* lop=cast<BinaryOperator>(lhs);
	    		auto *lvec = vec_map.GetVector(lop);
	    		errs()<<"get lvector:"<<*lvec<<"\n";   
	    		AllocaInst* rop=cast<AllocaInst>(rhs);
	    		auto *rvec = vec_map.GetVector(rop);
	    		errs()<<"get rvector:"<<*rvec<<"\n"; 
	    		auto store_val=builder.CreateStore(lvec,rvec);
                store_val->setAlignment(16);
	    		errs()<<"~~store_val:"<<*store_val<<"\n"; 
                //end of store
                //create mutiple of 3 
                Value *mul_value = ConstantInt::get(lop->getType() , 3); 
                errs()<<"~!!:"<<*mul_value<<"\n"; 
                //errs()<<"~!!!:"<<*mul_value<<"\n"; 
                auto *mul_three = builder.CreateMul(lop,mul_value);
                check_map.AddPair(lhs,mul_three);
                for (auto &U : lop->uses()) {
                  User *user = U.getUser();  // A User is anything with operands.
                  errs()<<*lop<<"-user:"<<*user<<"\n";
                  if(isa<StoreInst>(*user)){
                    //Value *mul_value = ConstantInt::get(op->getType() , 3); 
                    //auto *mul_three = builder.CreateMul(op,mul_value);
                    //op->replaceAllUsesWith(mul_three);
                    user->setOperand(U.getOperandNo(), mul_three);
                    errs()<<"ttt\n";
                  }
                  //user->setOperand(U.getOperandNo(), mul);
                }*/
                //op->eraseFromParent();
              //  BasicBlock::iterator it(I);
//it--;
//builder.SetInsertPoint(it);
                //IRBuilder<> builder1(op->getNextNode());
                //builder.SetInsertPoint(op->getNextNode());
                //StoreInst* store_three=builder.CreateStore(mul_three,rhs);
                //store_three->setAlignment(4);
                 //errs()<<"~~~store_three:"<<*store_three<<"\n";
                //StoreInst* instToReplace =  cast<StoreInst>(op); 
                //StoreInst* store_three = new StoreInst(mul_three,rhs);
              
                //store_three->setAlignment(4);
//BasicBlock::iterator BI(op);
//BasicBlock::iterator New(store_three);
                //errs()<<"~!!!op2:"<<*op<<"\n"; 
               // BI=New;
                //op->replaceAllUsesWith(store_three);
                //errs()<<"~!!!op2:"<<*op++<<"\n"; 
                //op->replaceAllUsesWith(store_three);
                /*errs()<<"~~~:"<<*lhs<<"\n";
                errs()<<"~~~:"<<*mul_three<<"\n";
                errs()<<"~!!!op2:"<<*op<<"\n"; 
                lop->replaceAllUsesWith(mul_three);
                errs()<<"~!!!op2:"<<*op<<"\n"; 
                //BasicBlock::iterator ii(op);*/
                //errs()<<"~!!!:"<<*store_three<<"\n"; 
                //errs()<<"~!!!:"<<op->getParent()<<"\n"; 
                //errs()<<"~!!!:"<<store_three->getParent()<<"\n"; 
         
            //BasicBlock::iterator BI(lop);
               //ReplaceInstWithValue(lop->getParent()->getInstList(),BI,mul_three);
                //ReplaceInstWithInst(op, store_three);
                //store_three->eraseFromParent();
                //errs()<<"~!!!op2:"<<*op<<"\n"; 
                //Instruction * insII = &I;
                //op->replaceAllUsesWith(store_three);
                //errs()<<"~!!!replaceAllUsesWith:"<<*op<<"\n"; 
                //op->dropAllReferences();
                //op->eraseFromParent();
                //op->removeFromParent();
               // errs()<<"~!!!eraseFromParen:"<<*op<<"\n"; 
                //errs()<<"~!!!:"<<*store_three<<"\n"; 
                //ReplaceInstWithInst(op,store_three);
                //ReplaceUnsafe(op,store_three);
                //op->replaceAllUsesWith(store_three);
                //op->eraseFromParent();
        }
        //Find load instruction & create vector before loadinst
        else if (auto *op = dyn_cast<LoadInst>(&I)) {
            BuilderAfterflag=0;
            BasicBlock::iterator instIt(I);
            IRBuilder<> builderafter(instIt->getParent(), ++instIt);
            ignoreuntilinst=instIt;
            errs()<<"*@@@@*set ignore point:"<<*instIt<<"\n";
            //IRBuilder<> builder(op);
            Value* loadinst_ptr=op->getPointerOperand();
            Type* load_ty= op->getType();
            /*Type* load_ty1= loadinst_ptr->getType();
            errs()<<"~Load type:"<<*load_ty<<"\n";
            errs()<<"~Load type1:"<<*load_ty1<<"\n";*/
            //errs()<<"*~Find Load_p:"<<*loadinst_ptr<<"\n";
            errs()<<"Tolerance:Create Vector Element:\n";
            Value* val = UndefValue::get(VectorType::get(load_ty, 4));
            //LoadInst* load_val=builder.CreateLoad(loadinst_ptr);
            //load_val->setAlignment(4);
            for (unsigned i = 0; i < 4; i++)//for 4 copies
            {
                //errs()<<"*****load_val:"<<*load_val<<"\n";
                //errs()<<"******:"<<*loadinst_ptr<<"\n";
       			//create insertelement instruction
				val = builderafter.CreateInsertElement(val,op, builderafter.getInt32(i));  
            }
            //get vector in map
            auto *vec = vec_map.GetVector(loadinst_ptr);
            //errs()<<"get vector:"<<*vec<<"\n";
            //errs()<<"get insertelement:"<<*val<<"\n";
            //create store into vector
            StoreInst* store_val=builderafter.CreateStore(val,vec);
            store_val->setAlignment(16);
            //errs()<<"create store:"<<*store_val<<"\n";
        }
        //Find operator to neon duplication
        else if (auto *op = dyn_cast<BinaryOperator>(&I)) {
            //errs()<<"Tolerance:Find BinaryOperator\n";
            auto op_name= I.getOpcodeName();
            // Insert at the point where the instruction `op` appears.
            IRBuilder<> builder(op);
            Value* lhs = op->getOperand(0);
	    	Value* rhs = op->getOperand(1);
            //errs()<<"lhs:"<<*lhs<<"\n";
	    	//errs()<<"rhs:"<<*rhs<<"\n";
            //Value *mul_value = ConstantInt::get(op->getType() , 3); 
            //Value* mul = builder.CreateMul(lhs, mul_value);
            Value* load_val1=GetVecOpValue(builder,lhs,vec_map);
            Value* load_val2=GetVecOpValue(builder,rhs,vec_map);
            if(strcmp(op_name, "add") == 0){// find op is "add"
		    //errs()<<"Find add:"<<op_name<<"\n";
                    if(load_val1!=NULL&&load_val2!=NULL) {
                    Value *vadd = builder.CreateAdd(load_val1,load_val2);
                    //errs()<<"Create add:"<<*vadd<<"\n";
                    //map add
 	                vec_map.AddPair(op, vadd);
                    }else{
                    errs()<<"Error: in ADD operator:"<<*op<<"\n";
                    }
            }
        

            //insert check
            for (auto &U : op->uses()) {
              User *user = U.getUser();  // A User is anything with operands.
              //errs()<<*op<<"-user:"<<*user<<"\n";
                if(isa<StoreInst>(*user)){
                BasicBlock::iterator instIt(I);
                IRBuilder<> builderafter(instIt->getParent(), ++instIt);
                errs()<<"*@@@@*Set ignore point:"<<*instIt<<"\n";
                ignoreuntilinst=instIt;
                Value *mul_value = ConstantInt::get(op->getType() , 3); 
                    //auto *mul_three = builder.CreateMul(op,mul_value);
                BuilderAfterflag=0;
                Value *mul = builderafter.CreateMul(op, mul_value);
                user->setOperand(U.getOperandNo(), mul);}
            }
            
          }
        }else{//builder after flag
                errs()<<"@@@@Ignore instruction:\n";
                I.dump();
                BasicBlock::iterator instIt(I);
                //errs()<<*<<"\n";
                if(++instIt==ignoreuntilinst){
                    errs()<<"*@@@@*Reset builderafter at:"<<*instIt<<"\n";
                    BuilderAfterflag=1;
                }
                //BuilderAfterflag=1;
            }
          //I.dump();
 
        }

        errs()<<"Show LLVM IR:\n";
        for (auto &I : B) {
            /*if (auto *op = dyn_cast<BinaryOperator>(&I)) {
                Value* New=check_map.GetVector(op);
                if(check_map.IsAdded(op)) {
                    IRBuilder<> builder(op);
            //Value* lhs = op->getOperand(0);
            //Value* rhs = op->getOperand(1);
            //Value* mul = builder.CreateMul(lhs, rhs);
                    op->replaceAllUsesWith(New);
                }
            }*/
            
            I.dump();
 
        }

      }
      PrintMap(&vec_map);
      PrintMap(&check_map);
      return true;
    }
  };
}

/**===================end of VectorizeMap========================/**/
char TolerancePass::ID = 0;
static RegisterPass<TolerancePass> X("tolerance", "Tolerance Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);

