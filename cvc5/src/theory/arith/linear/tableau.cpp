/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "base/output.h"
#include "theory/arith/linear/tableau.h"

using namespace std;
namespace cvc5::internal {
namespace theory {
namespace arith::linear {


void Tableau::pivot(ArithVar oldBasic, ArithVar newBasic, CoefficientChangeCallback& cb){
  Assert(isBasic(oldBasic));
  Assert(!isBasic(newBasic));
  Assert(d_mergeBuffer.empty());

  Trace("tableau") << "Tableau::pivot(" <<  oldBasic <<", " << newBasic <<")"  << endl;

  RowIndex ridx = basicToRowIndex(oldBasic);

  rowPivot(oldBasic, newBasic, cb);
  Assert(ridx == basicToRowIndex(newBasic));

  loadRowIntoBuffer(ridx);

  ColIterator colIter = colIterator(newBasic);
  while(!colIter.atEnd()){
    EntryID id = colIter.getID();
    Entry& entry = d_entries.get(id);

    ++colIter; //needs to be incremented before the variable is removed
    if(entry.getRowIndex() == ridx){ continue; }

    RowIndex to = entry.getRowIndex();
    Rational coeff = entry.getCoefficient();
    if(cb.canUseRow(to)){
      rowPlusBufferTimesConstant(to, coeff, cb);
    }else{
      rowPlusBufferTimesConstant(to, coeff);
    }
  }
  clearBuffer();

  //Clear the column for used for this variable

  Assert(d_mergeBuffer.empty());
  Assert(!isBasic(oldBasic));
  Assert(isBasic(newBasic));
  Assert(getColLength(newBasic) == 1);
}

/**
 * Changes basic to newbasic (a variable on the row).
 */
void Tableau::rowPivot(ArithVar basicOld, ArithVar basicNew, CoefficientChangeCallback& cb){
  Assert(isBasic(basicOld));
  Assert(!isBasic(basicNew));

  RowIndex rid = basicToRowIndex(basicOld);

  EntryID newBasicID = findOnRow(rid, basicNew);

  Assert(newBasicID != ENTRYID_SENTINEL);

  Tableau::Entry& newBasicEntry = d_entries.get(newBasicID);
  const Rational& a_rs = newBasicEntry.getCoefficient();
  int a_rs_sgn = a_rs.sgn();
  Rational negInverseA_rs = -(a_rs.inverse());

  for(RowIterator i = basicRowIterator(basicOld); !i.atEnd(); ++i){
    EntryID id = i.getID();
    Tableau::Entry& entry = d_entries.get(id);

    entry.getCoefficient() *=  negInverseA_rs;
  }

  d_basic2RowIndex.remove(basicOld);
  d_basic2RowIndex.set(basicNew, rid);
  d_rowIndex2basic.set(rid, basicNew);

  cb.multiplyRow(rid, -a_rs_sgn);
}

void Tableau::addRow(ArithVar basic,
                     const std::vector<Rational>& coefficients,
                     const std::vector<ArithVar>& variables)
{
  Assert(basic < getNumColumns());
  Assert(debugIsASet(variables));
  Assert(coefficients.size() == variables.size());
  Assert(!isBasic(basic));

  RowIndex newRow = Matrix<Rational>::addRow(coefficients, variables);
  addEntry(newRow, basic, Rational(-1));

  Assert(!d_basic2RowIndex.isKey(basic));
  Assert(!d_rowIndex2basic.isKey(newRow));

  d_basic2RowIndex.set(basic, newRow);
  d_rowIndex2basic.set(newRow, basic);
  
  // Initialize varTypes for quasi-basic support (migrated from OpenSMT)
  ensureVarTypesSize(basic);
  d_varTypes[basic] = VarType::BASIC;


  if(TraceIsOn("matrix")){ printMatrix(); }

  NoEffectCCCB noeffect;
  NoEffectCCCB* nep = &noeffect;
  CoefficientChangeCallback* cccb = static_cast<CoefficientChangeCallback*>(nep);

  vector<Rational>::const_iterator coeffIter = coefficients.begin();
  vector<ArithVar>::const_iterator varsIter = variables.begin();
  vector<ArithVar>::const_iterator varsEnd = variables.end();
  for(; varsIter != varsEnd; ++coeffIter, ++varsIter){
    ArithVar var = *varsIter;

    if(isBasic(var)){
      Rational coeff = *coeffIter;

      RowIndex ri = basicToRowIndex(var);

      loadRowIntoBuffer(ri);
      rowPlusBufferTimesConstant(newRow, coeff, *cccb);
      clearBuffer();
    }
  }

  if(TraceIsOn("matrix")) { printMatrix(); }

  Assert(debugNoZeroCoefficients(newRow));
  Assert(debugMatchingCountsForRow(newRow));
  Assert(getColLength(basic) == 1);
}

void Tableau::removeBasicRow(ArithVar basic){
  RowIndex rid = basicToRowIndex(basic);

  removeRow(rid);
  d_basic2RowIndex.remove(basic);
  d_rowIndex2basic.remove(rid);
}

void Tableau::substitutePlusTimesConstant(ArithVar to, ArithVar from, const Rational& mult,  CoefficientChangeCallback& cb){
  if(!mult.isZero()){
    RowIndex to_idx = basicToRowIndex(to);
    addEntry(to_idx, from, mult); // Add an entry to be cancelled out
    RowIndex from_idx = basicToRowIndex(from);

    cb.update(to_idx, from, 0, mult.sgn());

    loadRowIntoBuffer(from_idx);
    rowPlusBufferTimesConstant(to_idx, mult, cb);
    clearBuffer();
  }
}

uint32_t Tableau::rowComplexity(ArithVar basic) const{
  uint32_t complexity = 0;
  for(RowIterator i = basicRowIterator(basic); !i.atEnd(); ++i){
    const Entry& e = *i;
    complexity += e.getCoefficient().complexity();
  }
  return complexity;
}

double Tableau::avgRowComplexity() const{
  double sum = 0;
  uint32_t rows = 0;
  for(BasicIterator i = beginBasic(), i_end = endBasic(); i != i_end; ++i){
    sum += rowComplexity(*i);
    rows++;
  }
  return (rows == 0) ? 0 : (sum/rows);
}

void Tableau::printBasicRow(ArithVar basic, std::ostream& out){
  printRow(basicToRowIndex(basic), out);
}

// Quasi-basic variable support implementation
// Migrated from OpenSMT Tableau.cc

void Tableau::ensureVarTypesSize(ArithVar v) {
  while(static_cast<ArithVar>(d_varTypes.size()) <= v) {
    d_varTypes.push_back(VarType::NONE);
  }
}

void Tableau::normalizeRowForQuasiBasic(ArithVar v) {
  // This is a simplified version of OpenSMT's normalizeRow
  // In cvc5, we work with the matrix directly, so normalization
  // happens during pivot operations. This is mainly a placeholder
  // for future enhancements.
  Assert(isQuasiBasic(v));
  // The actual normalization is handled by the matrix structure
  // during pivot operations in cvc5
}

void Tableau::quasiToBasic(ArithVar v) {
  Assert(isQuasiBasic(v));
  
  // In cvc5, quasi-basic variables are those that have a row but
  // are not in d_basic2RowIndex. We need to ensure the row is properly
  // set up in the basic mapping.
  // Note: This is a simplified implementation. Full implementation would
  // need to rebuild column indices similar to OpenSMT.
  
  ensureVarTypesSize(v);
  d_varTypes[v] = VarType::BASIC;
  
  // The row should already exist in the matrix, we just need to
  // ensure it's tracked as basic. However, in cvc5's architecture,
  // rows are added via addRow() which sets up the basic mapping.
  // This method is mainly for converting existing quasi-basic vars.
  
  Trace("tableau::quasi") << "quasiToBasic(" << v << ")" << endl;
}

void Tableau::basicToQuasi(ArithVar v) {
  Assert(isBasic(v));
  
  // Remove from basic tracking but keep the row in the matrix
  // In cvc5, we can't easily remove the row without affecting
  // the matrix structure, so we mark it as quasi-basic but
  // keep the basic mapping for now.
  // Full implementation would remove column indices.
  
  ensureVarTypesSize(v);
  d_varTypes[v] = VarType::QUASIBASIC;
  
  // Note: In a full implementation, we would:
  // 1. Remove row from column indices (removeRowFromColumn)
  // 2. Keep the row in the matrix for later restoration
  
  Trace("tableau::quasi") << "basicToQuasi(" << v << ")" << endl;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
