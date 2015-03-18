//===-- Serializer.h --------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef __UTIL_SERIALIZER_H__
#define __UTIL_SERIALIZER_H__

#include <vector>
#include <cstdint>

#include "Serialization.capnp.h"

//#include "klee/util/ExprHashMap.h"
//#include "klee/util/ArrayExprHash.h"
#include "klee/Expr.h"
#include "klee/Config/config.h"

#include <capnp/common.h>
#include <capnp/message.h>
#include <capnp/orphan.h>
#include <unordered_map>

namespace klee {
class Query;

typedef capnp::Orphan<serialization::Expr> ExprSz;
typedef capnp::Orphan<serialization::Array> ArraySz;
typedef capnp::Orphan<serialization::UpdateNode> UpdateNodeSz;

//class SerializedArrayExprHash : public ArrayExprHash<uint32_t> {
//    
//    friend class Serializer;
//    
//  public:
//    SerializedArrayExprHash() {};
//    virtual ~SerializedArrayExprHash() {};
//    void clear(){
//      _array_hash.clear();
//      _update_node_hash.clear();
//    }
//};

class Serializer {
private:  
  std::vector<ExprSz> exprList;
  std::vector<ArraySz> arrayList;
  std::vector<UpdateNodeSz> updateNodeList;

//  ExprHashMap< std::pair<uint32_t, uint32_t> > exprCache;
//  SerializedArrayExprHash arrayCache;
  std::unordered_map<unsigned, std::pair<uint32_t, uint32_t> > exprCache;
  std::unordered_map<unsigned, uint32_t> arrayCache;
  std::unordered_map<unsigned, uint32_t> updateNodeCache;

  uint32_t getInitialArray(const Array *os, capnp::Orphanage& orphanage);
  uint32_t getArrayForUpdate(const Array *root, const UpdateNode *un, capnp::Orphanage& orphanage);

  uint32_t serialize(ref<Expr> e, int *width_out, capnp::Orphanage& orphanage, bool secretSwitch = false);
  uint32_t serializeCastExpr(ref<Expr> e, serialization::Expr::Kind kind, int* width_out, capnp::Orphanage& orphanage);
  template<typename T> uint32_t serializeBinaryExpr(ref<Expr> e, serialization::Expr::Kind kind, int* width_out, bool onlyBoolWidthOut, capnp::Orphanage& orphanage);
  template<typename T> uint32_t serializeShiftExpr(ref<Expr> e, serialization::Expr::Kind kind, int* width_out, capnp::Orphanage& orphanage);
  template<typename T> uint32_t serializeCmpExpr(ref<Expr> e, serialization::Expr::Kind kind, int* width_out, bool onlyBoolWidthOut, capnp::Orphanage& orphanage);
  uint32_t serializeConstant();
  uint32_t serializeActual(ref<Expr> e, int *width_out, capnp::Orphanage& orphanage);
  
public:
  capnp::MessageBuilder&& serialize(const Query& query, const std::vector<const Array*>& objects, capnp::MessageBuilder&& message);
};

}

#endif
