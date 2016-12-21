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
#include "llvm/IR/LLVMContext.h"
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
    int GetSize(){
        return vmap.size();
    }
  };
  void PrintMap(VectorizeMap *map)
  {
        errs() <<"(size = "<<map->GetSize()<<")\n";
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
      VectorizeMap recovery_map;
      static LLVMContext TheContext;
      AllocaInst* recovery;
      BasicBlock::iterator ignoreuntilinst;
      for (auto &B : F) {
        //errs() << "Basic block:\n";
        //B.dump();
        bool BuilderAfterflag=1;
        for (auto &I : B) {
        //BasicBlock* bb=I.getParent();
        //Find allocation instruction
        if (BuilderAfterflag) {
        if (auto *op = dyn_cast<AllocaInst>(&I)) {
            //errs()<< "Tolerance:Find AllocaInst!\n";
            
            IRBuilder<> builder(op);
            
            Type* scalar_t= op->getAllocatedType();//not pointer
            //Type* scalar_t1= op->getType();//pointer
            errs()<<*scalar_t<<"\n";
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
        
        }
        //Find load instruction & create vector before loadinst
        else if (auto *op = dyn_cast<LoadInst>(&I)) {
            BuilderAfterflag=0;
            BasicBlock::iterator instIt(I);
            IRBuilder<> builderafter(instIt->getParent(), ++instIt);
            ignoreuntilinst=instIt;
            //errs()<<"*@@@@*set ignore point:"<<*instIt<<"\n";
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

            /**Find Check Point**/
            for (auto &U : op->uses()) {
              User *user = U.getUser();  // A User is anything with operands.
              Value* v= U.get();
              //errs()<<"*!@**@***!@****!@**"<<*v<<"\n";
              //errs()<<*op<<"-user:"<<*user<<"\n";
                if(isa<StoreInst>(*user)){//Find final store 
                //Instruction* op1 = cast<Instruction>(v);
                //if(auto *op1 = dyn_cast<StoreInst>(*user)){//Find final store 
                BasicBlock::iterator instIt(I);
                IRBuilder<> builderafter(instIt->getParent(), ++instIt);
                //errs()<<"*@@@@*Set ignore point:"<<*instIt<<"\n";
                ignoreuntilinst=instIt;
                Value *mul_value = ConstantInt::get(op->getType() , 3); //only integer!!!
                BuilderAfterflag=0;
                Value *mul = builderafter.CreateMul(op, mul_value);
                //create load vector
                Value* final_store=user->getOperand(1);
                //errs()<<"*XXXXX*:"<<*user->getOperand(1)<<"\n";
                auto *vec = vec_map.GetVector(final_store);
                auto *op_vec = vec_map.GetVector(op);
                //create final store vector
                auto* store_vec=builder.CreateStore(op_vec,vec);
                auto* load_vec=builder.CreateLoad(vec);//before is ok
                load_vec->setAlignment(4);
                //create sum of three copies
                uint64_t lane0= 0;
                uint64_t lane1= 1;
                uint64_t lane2= 2;
                auto *ex0=builder.CreateExtractElement(load_vec,lane0,"extract0");
                auto *ex1=builder.CreateExtractElement(load_vec,lane1,"extract1");
                auto *ex2=builder.CreateExtractElement(load_vec,lane2,"extract2");
                Instruction* recoveryinst=cast<Instruction>(ex2);
                recovery=builder.CreateAlloca(recoveryinst->getType(),nullptr,"recovery");
                recovery->setAlignment(4);
                Value *vadd = builder.CreateAdd(ex0,ex1);
                Value *vadd1 = builder.CreateAdd(vadd ,ex2);
                //chech create after mutltiple 3
                Value *fault_check=builderafter.CreateICmpNE(vadd1,mul);
                //errs()<<"****"<<*user<<"\n";
                check_map.AddPair(user,fault_check);
                check_map.AddPair(fault_check,ex0);
                recovery_map.AddPair(user,op);
                //TerminatorInst *ThenTerm = nullptr, *ElseTerm = nullptr;
                //BasicBlock::iterator it(op1);

                //TerminatorInst *ThenTerm , *ElseTerm ;

                //SplitBlockAndInsertIfThenElse(fault_check, op1, &ThenTerm, &ElseTerm,nullptr);
                //builderafter.SetInsertPoint(ThenTerm);
 
                //builderafter.SetInsertPoint(ElseTerm);
                //user->setOperand(U.getOperandNo(), mul);//final store
            }
            }
            
          }
        } else{//builder after flag
                //errs()<<"@@@@Ignore instruction:\n";
                I.dump();
                BasicBlock::iterator instIt(I);
                //errs()<<*<<"\n";
                if(++instIt==ignoreuntilinst){
                    //errs()<<"*@@@@*Reset builderafter at:"<<*instIt<<"\n";
                    BuilderAfterflag=1;
                }
                //BuilderAfterflag=1;
            }
          //I.dump();
 
        }
       
        
        

      }
      errs()<<"Start Insert Check!\n";
      for(int i =0 ; i<check_map.GetSize(); i++){
          bool check_flag=0;
          for (auto &B : F) {
                //B.dump();
                for (auto &I : B) {
                    //insert check before store
                    if (StoreInst *op = dyn_cast<StoreInst>(&I)) {
                        if(check_map.IsAdded(op)){
                            //errs()<<"Tolerance:Find BinaryOperator\n";
                            auto op_name= I.getOpcodeName();
                            // Insert at the point where the instruction `op` appears.
                            IRBuilder<> builder(op);
        
                            Value *fault_check = check_map.GetVector(op);
                            Value *ex0 = check_map.GetVector(fault_check);
                            Instruction* faultinst=cast<Instruction>(fault_check);
                            Value* lhs = faultinst->getOperand(0);
                            Value* rhs = faultinst->getOperand(1);
                           
                            errs()<<"before op:"<<*op<<"\n";    
                            errs()<<"insert fault check:"<<*fault_check<<"\n";    
                            errs()<<"lhs:"<<*lhs<<"\n"; 
                            errs()<<"rhs:"<<*rhs<<"\n";  
                            errs()<<"ex0:"<<*ex0<<"\n";   
                            //TerminatorInst *ThenTerm , *ElseTerm ;
                            TerminatorInst* checkTerm = SplitBlockAndInsertIfThen(fault_check, op,false);
                            //SplitBlockAndInsertIfThenElse(fault_check, op, &ThenTerm, &ElseTerm,nullptr);
                            IRBuilder<> builderCheck(checkTerm);
                            //Taking mul_three value div by ex0, because only Interger can use Rem operator.
                            //Inter use SDIV, Float use FDIV.
                            Value* mod_three = builderCheck.CreateSDiv(lhs,ex0,"rem3");
                            
                            Instruction* ty= cast<Instruction>(mod_three);
                            Value *mul_value = ConstantInt::get(ty->getType() , 3); //only integer!!!
                           
                            errs()<<"mod_three:"<<*mod_three<<"\n";   
                            errs()<<"mul_value :"<<*mul_value <<"\n";   
                            //cmp div ex0 = 3
                            Value* cmp_three = builderCheck.CreateICmpNE(mod_three,mul_value);
                            //for ( BasicBlock::iterator i = checkTerm->begin(), e = checkTerm->end();i!= e; ++i)
                            errs()<<"end"<<*checkTerm<<"\n";   
                            //Then = div 3 can recovery
                            TerminatorInst *ThenTerm , *ElseTerm ;
                            SplitBlockAndInsertIfThenElse(cmp_three, checkTerm, &ThenTerm, &ElseTerm,nullptr);
                            IRBuilder<> builderRecovery(ThenTerm);
                            auto* store_recovery=builderRecovery.CreateStore(ex0,recovery);
                            store_recovery->setAlignment(4);
                            //Else = original i
                            IRBuilder<> builderRecoveryElse(ElseTerm);                           
                            Value *recovery_val = recovery_map.GetVector(op);
                            auto* store_recoveryElse=builderRecoveryElse.CreateStore(recovery_val,recovery);
                            store_recoveryElse->setAlignment(4);
                            check_flag=1;
                          
                            ////user->setOperand(U.getOperandNo(), mul);//final store
                        }
                    }
                    
                    if(check_flag)
                       break;
                    }
                    
                
                break;
            }
      }
      //replace recovery value to store
     for (auto &B : F) {
                //B.dump();
                for (auto &I : B) {
                    //insert check before store
                    if (StoreInst *op = dyn_cast<StoreInst>(&I)) {
                        if(check_map.IsAdded(op)){
                            IRBuilder<> builder(op);
                            auto* load_recovery=builder.CreateLoad(recovery);
                            load_recovery->setAlignment(4);
                            op->setOperand(0, load_recovery);
                        }
                    }
                }
            }
      errs()<<"Show LLVM IR:\n";
      for (auto &B : F) {
            B.dump();
            for (auto &I : B) {
              //I.dump;
          }
        }
      errs()<<"Vector Map:\n";
      PrintMap(&vec_map);
      errs()<<"Check Map:\n";
      PrintMap(&check_map);
      errs()<<"Recovery Map:\n";
      PrintMap(&recovery_map);
    
      //PrintMap(&check_map);
      return true;
    }
  };
}

/**===================end of VectorizeMap========================/**/
char TolerancePass::ID = 0;
static RegisterPass<TolerancePass> X("tolerance", "Tolerance Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);

