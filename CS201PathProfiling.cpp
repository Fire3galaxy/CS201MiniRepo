/*
 * Authors: Name(s) <email(s)>
 * 
 */

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/ADT/iterator.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/IR/CFG.h"
#include <stack>
#include <set>
#include <iostream>
#include <string>

using namespace llvm;

namespace {

  static Function* printf_prototype(LLVMContext& ctx, Module *mod) {
    std::vector<Type*> printf_arg_types;
    printf_arg_types.push_back(Type::getInt8PtrTy(ctx));
 
    FunctionType* printf_type = FunctionType::get(Type::getInt32Ty(ctx), printf_arg_types, true);
    Function *func = mod->getFunction("printf");
    if(!func)
      func = Function::Create(printf_type, Function::ExternalLinkage, Twine("printf"), mod);
    func->setCallingConv(CallingConv::C);
    return func;
  }

  struct CS201PathProfiling : public DominatorTreeWrapperPass {
  static char ID;
  //CS201PathProfiling() : FunctionPass(ID) {}
	LLVMContext *Context;

    GlobalVariable *bbCounter = NULL;
    GlobalVariable *BasicBlockPrintfFormatStr = NULL;
    Function *printf_func = NULL;

    // For edge profiling
    GlobalVariable *edge_cnt_array = NULL;
    GlobalVariable *edgeFormatStr1 = NULL;
    GlobalVariable *edgeFormatStr2 = NULL;
    GlobalVariable *zeroVar = NULL;

    std::vector<std::set<BasicBlock *> > loop_vector;
    std::vector<bool> is_innermost;

    //----------------------------------
    bool doInitialization(Module &M) {
      errs() << "\n---------Starting BasicBlockDemo---------\n";
      Context = &M.getContext();
      bbCounter = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, 
          ConstantInt::get(Type::getInt32Ty(*Context), 0), "bbCounter");
      const char *finalPrintString = "BB Count: %d\n";
      Constant *format_const = ConstantDataArray::getString(*Context, finalPrintString);
      BasicBlockPrintfFormatStr = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), 
          strlen(finalPrintString)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "BasicBlockPrintfFormatStr");
      printf_func = printf_prototype(*Context, &M);

      // Edge Profiling Setup
      // edge str 1 and 2
      const char *edgeStr1 = "EDGE PROFILING:\n";
      format_const = ConstantDataArray::getString(*Context, edgeStr1);
      edgeFormatStr1 = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), 
          strlen(edgeStr1)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "edgeFormatStr1");

      const char *edgeStr2 = "b%d -> b%d: %d\n";
      format_const = ConstantDataArray::getString(*Context, edgeStr2);
      edgeFormatStr2 = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), 
          strlen(edgeStr2)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "edgeFormatStr2");

      // edge_cnt_array size: Need a global int array to profile edges. Gonna just make 1 array for all functions.
      // Next time: Traverse the edges in the order that you traverse the blocks for each function. That way, the
      // order stays the same because the for loop stays the same. Then just make an array for the largest edge 
      // count. 
      int bb_tmp = 0;
      int max_num_edges = 0;
      int num_edges = 0;
      // Go through each function
      for (auto& f : M) {
        // Go through each bb
        for (auto& bb : f) {
          // go through successors of bb
          succ_iterator end = succ_end(&bb);
          for (succ_iterator sit = succ_begin(&bb);sit != end; ++sit) {
            num_edges++;  
          }
        }
        if (num_edges > max_num_edges) max_num_edges = num_edges;
      }

      // edge_cnt_array: Declaring the actual int array of size max_num_blocks
      llvm::ArrayType* edgeArrayType = llvm::ArrayType::get(llvm::IntegerType::get(*Context, 32), max_num_edges);
      edge_cnt_array = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 32), max_num_edges), 
          false, llvm::GlobalValue::PrivateLinkage, ConstantArray::get(edgeArrayType, 
          ConstantInt::get(Type::getInt32Ty(*Context), 0)), "edge_cnt_array");

      // bb src, dst, and zero
      zeroVar = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, 
          ConstantInt::get(Type::getInt32Ty(*Context), 0), "zeroVar");
 
      errs() << "Module: " << M.getName() << "\n";
 
      return true;
    }
 
    //----------------------------------
    bool doFinalization(Module &M) {
    //all loops with an is_innermost value of true at this point are innermost loops
      for(int i; i < is_innermost.size(); i++ ){
      	if(is_innermost[i]){
      		errs() <<  printLoop(loop_vector[i], "Innermost Loop")<< '\n';
      	}
      }
      errs() << "-------Finished BasicBlocksDemo----------\n";
 
      return false;
    }

    //----------------------------------
    bool runOnFunction(Function &F) override {
    	int bbname_int=0;
      for(auto &BB: F) {
          std::string test="b"+(std::to_string(bbname_int));
          Twine bbname= Twine(test);
          BB.setName(bbname);
          bbname_int++;
      }

      DominatorTreeWrapperPass::runOnFunction(F);

      errs() << "Function: " << F.getName() << '\n';

      for(auto &BB: F) {
        // Add the footer to Main's BB containing the return 0; statement BEFORE calling runOnBasicBlock
        if(F.getName().equals("main") && isa<ReturnInst>(BB.getTerminator())) { // major hack?
          addFinalPrintf(BB, Context, bbCounter, BasicBlockPrintfFormatStr, printf_func);
        }
        runOnBasicBlock(BB);
      }

      //check all loops in loop vector to identify innermost loop
      for(int i=0; i<loop_vector.size(); i++){
      	if(is_innermost[i]){
	      	for(int j=0; j<loop_vector.size(); j++){
	      		if(j!=i){
	      			bool all_contained=true;
	      			for(auto &m : loop_vector.at(i)){
	      				if(loop_vector[j].find(m) == loop_vector.at(j).end()){
	      					all_contained=false;
	      					break;
	      				}

	      			}

	      			if(all_contained){
	      				is_innermost[j]=false;
	      			}
	      		}
	      	}
	    }
      }

      // Add edge profiling code to CFG. (Adds a ton of extra basicBlocks, so I want to do this after
      // path profiling).
      insertAllEdgeNodes(F);
      insertEdgeInstrumentation(F);

      // add printf calls for Edge Profile instrumentation
      addEdgeProfilePrints(F, Context, F.size(), printf_func);
 
      return true; 
    }

    bool runOnBasicBlock(BasicBlock &BB) {
      errs() << "BasicBlock: " << BB.getName() << '\n';
      IRBuilder<> IRB(BB.getFirstInsertionPt()); // Will insert the generated instructions BEFORE the first BB instruction
      Value *loadAddr = NULL, *addAddr = NULL;

      // BBCounter's increment instruction
      loadAddr = IRB.CreateLoad(bbCounter);
      addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
      IRB.CreateStore(addAddr, bbCounter);

      succ_iterator end = succ_end(&BB);
      for (succ_iterator sit = succ_begin(&BB);sit != end; ++sit){
        //errs() << "Successor to "+BB.getName()+": " << sit->getName()<< '\n';

        //found a back edge
        if (getDomTree().dominates(sit->getTerminator(), &BB)){
        	std::stack<BasicBlock *> s;
        	std::set<BasicBlock *> loop;
      		loop.insert(*sit);
      		loop.insert(&BB);
      		s.push(&BB);

      		while(!s.empty()){

      			BasicBlock* m= s.top();
      			s.pop();
      			pred_iterator end_pred_iterator = pred_end(m);
      			for (pred_iterator pit = pred_begin(m);pit != end_pred_iterator; ++pit){
      				if(loop.find(*pit)==loop.end()){
      					s.push(*pit);
      					loop.insert(*pit);
      				}
      			}

      		}

      		//add loop to loop vector
      			loop_vector.push_back(loop);
      			is_innermost.push_back(true);

        }



      }
 
      for(auto &I: BB)
        errs() << I << "\n";
 
      return true;
    }

    std::string printLoop(std::set<BasicBlock *> loop, std::string label){
    	std::string formatted_loop=label+": {";
  		std::string comma="";
  		for(std::set<BasicBlock *>::iterator it=loop.begin(); it!=loop.end(); ++it){
  			formatted_loop=(formatted_loop+(comma+((*it)->getName()).str()));
  			comma=",";
  		}
  		formatted_loop+="}";

  		return formatted_loop;
    }

     //----------------------------------
    // Rest of this code is needed to: printf("%d\n", bbCounter); to the end of main, just BEFORE the return statement
    // For this, prepare the SCCGraph, and append to last BB?
    void addFinalPrintf(BasicBlock& BB, LLVMContext *Context, GlobalVariable *bbCounter, GlobalVariable *var, Function *printf_func) {
      IRBuilder<> builder(BB.getTerminator()); // Insert BEFORE the final statement
      std::vector<Constant*> indices;
      Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(*Context));
      indices.push_back(zero);
      indices.push_back(zero);
      Constant *var_ref = ConstantExpr::getGetElementPtr(var, indices);
 
      Value *bbc = builder.CreateLoad(bbCounter);
      CallInst *call = builder.CreateCall2(printf_func, var_ref, bbc);
      call->setTailCall(false);
    }

    // Copy of above function for various integer arguments to print. Named after CreateCall2 style
    // MUST PASS IRBuilder OBJECT TO THESE
    void addFinalPrintf3(BasicBlock& BB, LLVMContext *Context, Value *arg1, Value *arg2, 
          Value *arg3, GlobalVariable *var, Function *printf_func) {
      IRBuilder<> builder(BB.getTerminator()); // Insert BEFORE the final statement
      std::vector<Constant*> indices;
      Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(*Context));
      indices.push_back(zero);
      indices.push_back(zero);
      Constant *var_ref = ConstantExpr::getGetElementPtr(var, indices);
 
      CallInst *call = builder.CreateCall4(printf_func, var_ref, arg1, arg2, arg3);
      call->setTailCall(false);
    }

    void addFinalPrintf0(BasicBlock& BB, LLVMContext *Context, GlobalVariable *var, Function *printf_func) {
      IRBuilder<> builder(BB.getTerminator()); // Insert BEFORE the final statement
      std::vector<Constant*> indices;
      Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(*Context));
      indices.push_back(zero);
      indices.push_back(zero);
      Constant *var_ref = ConstantExpr::getGetElementPtr(var, indices);
 
      CallInst *call = builder.CreateCall(printf_func, var_ref);
      call->setTailCall(false);
    }

    void addEdgeProfilePrints(Function& F, LLVMContext *Context, int numBlocks, Function *printf_func) {
      // Don't run for functions with no edges
      if (F.size() <= 1)
        return;

      // Get exit block for function F (need for IRBuilder hack)
      BasicBlock* exitBlock = NULL;
      for(auto &B: F) {
        if(isa<ReturnInst>(B.getTerminator())) { 
          exitBlock = &B;
        }
      }

      // Output first line
      IRBuilder<> IRB(exitBlock->getTerminator()); // Insert BEFORE the final statement
      addFinalPrintf0(*exitBlock, Context, edgeFormatStr1, printf_func);

      // Load zero into Value*
      Value* zeroVarVal = IRB.CreateLoad(zeroVar);

      // Output each edge
      for (auto& BB : F) {
        std::string bbname = BB.getName();

        // Only look at edge nodes
        if (bbname.size() >= 7 && bbname.substr(0,7) == "bb_edge") {
          // Get edge count into Value*
          const char* nodeName = bbname.c_str();
          int64_t nodeIdx = std::atoi(nodeName + 7); // ignore "bb_edge"
          Value *edgeCnt = getEdgeFreq(IRB, nodeIdx);

          // Get edge index into Value*
          Value* edgeIndex = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), nodeIdx), zeroVarVal);

          // Get source node index into Value*
          nodeName = BB.getUniquePredecessor()->getName().str().c_str();
          nodeIdx = std::atoi(nodeName + 1); // ignore 'b'
          Value* srcIndex = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), nodeIdx), zeroVarVal);

          // Get dst node index into Value*
          nodeName = BB.getTerminator()->getSuccessor(0)->getName().str().c_str();
          nodeIdx = std::atoi(nodeName + 1); // ignore 'b'
          Value* dstIndex = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), nodeIdx), zeroVarVal);

          // Print edge count
          addFinalPrintf3(*exitBlock, Context, srcIndex, dstIndex, edgeCnt, edgeFormatStr2, printf_func);
        }
      }
    }

    Value* getEdgeFreq(IRBuilder<> IRB, int blockIdx) {
      Value* idxList[2] = {
        ConstantInt::get(Type::getInt32Ty(*Context), 0), 
        ConstantInt::get(Type::getInt32Ty(*Context), blockIdx)
      };
      Value *bbPtr = IRB.CreateGEP(edge_cnt_array, ArrayRef<Value*>(idxList, 2));
      return IRB.CreateLoad(bbPtr);
    }

    Value* getEdgeFreqPtr(IRBuilder<> IRB, int blockIdx) {
      Value* idxList[2] = {
        ConstantInt::get(Type::getInt32Ty(*Context), 0), 
        ConstantInt::get(Type::getInt32Ty(*Context), blockIdx)
      };
      return IRB.CreateGEP(edge_cnt_array, ArrayRef<Value*>(idxList, 2));
    }

    void insertEdgeInstrumentation(Function &F) {
      for (auto &BB : F) {
        std::string bbname = BB.getName().str();

        // Only look at non-edge nodes
        if (bbname.size() < 7 || bbname.substr(0,7) != "bb_edge") {
          // Iterate through connected edge nodes (always children of regular nodes)
          // Inserts instrumentation node for each edge
          succ_iterator end = succ_end(&BB);
          for (succ_iterator sit = succ_begin(&BB);sit != end; ++sit) {
            IRBuilder<> IRB(sit->begin());
            Value* loadAddr = IRB.CreateLoad(zeroVar);

            // Get successor index into Value*
            const char* blockName = sit->getName().str().c_str();
            int64_t blockIdx = std::atoi(blockName + 7); // ignore "bb_edge"
            Value* srcAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), blockIdx), loadAddr);

            // Get array elem ptr edge count into Value*
            Value *edgePtr = getEdgeFreqPtr(IRB, blockIdx);
            loadAddr = IRB.CreateLoad(edgePtr);

            // Access array and increment count
            Value* addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
            IRB.CreateStore(addAddr, edgePtr);
          }
        } 
      }
    }

    void insertAllEdgeNodes(Function &F) {
      for (auto& BB : F) {
        std::string bbname = BB.getName();

        if (bbname.length() < 7 || bbname.substr(0, 7) != "bb_edge") {
          succ_iterator end = succ_end(&BB);

          // Iterate through successors and split edges
          for (succ_iterator sit = succ_begin(&BB); sit != end; ++sit) {
            // Is not an edge node
            if (sit->getName().str().length() < 7 || sit->getName().str().substr(0, 7) != "bb_edge") {
              insertEdgeNode(bbname, *sit);
            }
          }
        }
      }
    }

    void insertEdgeNode(std::string srcNodeName, BasicBlock* currDstNode) {
      Twine edgeName = Twine("bb_edge");

      // The child becomes the "edge" node (save name to give to child node)
      std::string succName = currDstNode->getName();
      currDstNode->setName(edgeName);

      // The newly split node becomes the "child" node because split
      // gives the instructions to the new node 
      BasicBlock *newDstNode = currDstNode->splitBasicBlock(currDstNode->begin(), succName);

      // Fix predecessors to point to node still, not to edge
      pred_iterator end_pred_iterator = pred_end(currDstNode);
      for (pred_iterator pit = pred_begin(currDstNode);pit != end_pred_iterator; ++pit) {
      	// Change successors of nodes besides the current node
      	if ((*pit)->getName().str() != srcNodeName) {
      	  // Iterate through successors of the predecessor node (only want to change 1 successor)
      	  TerminatorInst* terminator = (*pit)->getTerminator();
      	  for (int i = 0; i < terminator->getNumSuccessors(); i++) {
      	    if (terminator->getSuccessor(i)->getName() == currDstNode->getName()) {
      	      terminator->setSuccessor(i, newDstNode);
      	      break;
      	    }
      	  }
      	}
      }
    }

    void debugPrintFunction(Function &F) {
      // Print every block in CFG
      for (auto &BB : F) {
        errs() << BB.getName() << '\n';
        // Print outgoing edges
        succ_iterator end = succ_end(&BB);
        for (succ_iterator sit = succ_begin(&BB);sit != end; ++sit) {
          errs() << '\t' << sit->getName() << '\n';
        }
      }
    }

  };
}

char CS201PathProfiling::ID = 0;
static RegisterPass<CS201PathProfiling> X("pathProfiling", "CS201PathProfiling Pass", false, false);

