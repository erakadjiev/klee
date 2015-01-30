//===-- SMTLIBOutputLexer.cpp ------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "SMTLIBOutputLexer.h"
#include <ctype.h>
#include <errno.h>
#include <cstdlib>

namespace klee
{

	SMTLIBOutputLexer::SMTLIBOutputLexer() :
			input(NULL),lastTokenContents(""),
			lastNumericTokenValue(""), lastChar(' '),
			lastNumericToken(UNRECOGNISED_TOKEN),
			tokenToReturn(NULL)
	{
	}

	bool SMTLIBOutputLexer::getNextToken(Token& t)
	{
		if(input==NULL)
			return false;

		if(! input->good())
			return false;


		//clear the last token string
		lastTokenContents="";

		tokenToReturn=&t;

		/* We set lastChar like this so that the call to walkPastWhiteSpace()
		 * will walk past the whitespace and have lastChar set to the next
		 * non-whitespace character.
		 */
		lastChar=' ';

		//skip whitespace and newlines
		if(!walkPastWhiteSpace())
			return true;

		//now lastChar contains a useful character

		//Check for #b or #x
		if(lastChar =='#')
		{

			lastTokenContents=lastChar;
			lastTokenContents+= input->get();

			if(lastTokenContents=="#b")
			{
				//we should have a binary numeral

				//check there are digits that follow
				lastChar=input->peek();
				if(lastChar != '0' && lastChar != '1')
				{
					*tokenToReturn = UNRECOGNISED_TOKEN;
					return false;
				}

				//clear the lastNumeric number
				lastNumericTokenValue="";

				//gather digits (lastChar peeks ahead)
				while(lastChar == '0' || lastChar == '1')
				{
					lastNumericTokenValue+=input->get(); //move input forward
					lastChar=input->peek();
				}

				//append the digits to what we've already found.
				lastTokenContents+=lastNumericTokenValue;

				//we should gathered all the bits now
				*tokenToReturn = lastNumericToken= NUMERAL_BASE2_TOKEN;
				return true;
			}
			else if(lastTokenContents=="#x")
			{
				//we should have a hex numeral

				//check there hex digits to follow
				lastChar=input->peek();
				if(!isxdigit(lastChar))
				{
					*tokenToReturn = UNRECOGNISED_TOKEN;
					return false;
				}

				//clear the lastNumeric number
				lastNumericTokenValue="";

				//gather hex digits (lastChar peeks ahead)
				while(isxdigit(lastChar))
				{
					lastNumericTokenValue+=input->get(); //move input forward
					lastChar=input->peek();
				}

				//append the digits to what we've already found.
				lastTokenContents+=lastNumericTokenValue;

				//we should have gathered all the hex digits now
				*tokenToReturn = lastNumericToken = NUMERAL_BASE16_TOKEN;
				return true;
			}
			else
			{
				*tokenToReturn = UNRECOGNISED_TOKEN;
				return false;
			}
		}

		if(lastChar ==')')
		{
			*tokenToReturn = RBRACKET_TOKEN;
			lastTokenContents=lastChar;
			return true;
		}

		//could be "(" or "(_ bvN  N)"
		if(lastChar == '(')
		{
			if(input->peek() != '_')
			{
				//It's just a left bracket
				*tokenToReturn = LBRACKET_TOKEN;
				lastTokenContents=lastChar;
				return true;
			}

			lastTokenContents="";
			lastTokenContents+=lastChar;
			lastChar=input->get();
			lastTokenContents+=lastChar;

			//now have "(_" so far

			//walkpast any whitespace
			lastChar=input->get();
			if(!walkPastWhiteSpace())
			{
				//we didn't expect to hit EOF here
				return false;
			}

			lastTokenContents+=" "; //add a space because none have been added so far.

			//at this point lastChar is a non-whitespace and the stream points to the character afterwards

			//expecting "bv"
			lastTokenContents+=lastChar;
			lastChar=input->get();
			lastTokenContents+=lastChar;

			if(lastTokenContents != "(_ bv")
			{
				*tokenToReturn = UNRECOGNISED_TOKEN;
				return false;
			}

			//have "(_ bv" so far.

			//the next character should be the start of the digits ( the actual numeric value in base10)
			lastChar=input->get();
			if(!isdigit(lastChar))
			{
				*tokenToReturn = UNRECOGNISED_TOKEN;
				return false;
			}

			//clear the lastNumericToken value
			lastNumericTokenValue="";
			lastNumericTokenValue+=lastChar; //grab the first digit

			//gather other digits (there might not be any) (lastChar peeks ahead)
			lastChar=input->peek();
			while(isdigit(lastChar))
			{
				lastNumericTokenValue+=input->get(); //move input forward
				lastChar=input->peek();
			}

			lastTokenContents+=lastNumericTokenValue;

			//walkpast any whitespace
			if(!walkPastWhiteSpace())
			{
				//we didn't expect to hit EOF here
				return false;
			}
			lastTokenContents+=" ";//append a single space

			//have "(_ bvN " so far where N is a decimal number.

			//now comes the digit stating the bit width we don't care what this number actually is
			//lastChar should be pointing at a numeral
			if(!isdigit(lastChar))
			{
				*tokenToReturn = UNRECOGNISED_TOKEN;
				return false;
			}

			lastTokenContents+=lastChar;//grab the digit

			//grab the other digits (if they exist)
			lastChar=input->peek();
			while(isdigit(lastChar))
			{
				lastTokenContents+=input->get(); //move input forward
				lastChar=input->peek();
			}

			lastChar=input->get(); //move forward one so stream points ahead of lastChar

			//walkpast any whitespace
			if(!walkPastWhiteSpace())
			{
				//we didn't expect to hit EOF here
				return false;
			}

			//now the last character should be ')'
			if(lastChar != ')')
			{
				*tokenToReturn = UNRECOGNISED_TOKEN;
				return false;
			}
			lastTokenContents+=lastChar;

			//Finally processed the bitvector
			*tokenToReturn = lastNumericToken = NUMERAL_BASE10_TOKEN;
			return true;
		}

		/* Could be SAT, UNSAT, UNKNOWN, SELECT or ARRAY_IDENTIFIER
		 *
		 */
		if(isalpha(lastChar))
		{
			lastTokenContents+=lastChar;

			//grab additional characters (there may be none)
			lastChar=input->peek();
			while(isIdentifier(lastChar))
			{
				lastChar=input->get();
				lastTokenContents+=lastChar;
				lastChar=input->peek();

				/* Check for keywords. We look ahead one character to check that we're not accidently
				 * identifying an ARRAY_IDENTIFIER that uses another keyword as a prefix.
				 * e.g. an array called sat_1 could be identified as SAT if we didn't look ahead.
				 */
				if(lastTokenContents == "sat" && !isIdentifier(input->peek()))
				{
					*tokenToReturn = SAT_TOKEN;
					return true;
				}

				if(lastTokenContents == "unsat" && !isIdentifier(input->peek()))
				{
					*tokenToReturn = UNSAT_TOKEN;
					return true;
				}

				if(lastTokenContents == "unknown" && !isIdentifier(input->peek()))
				{
					*tokenToReturn = UNKNOWN_TOKEN;
					return true;
				}

				if(lastTokenContents == "select" && !isIdentifier(input->peek()))
				{
					*tokenToReturn = SELECT_TOKEN;
					return true;
				}


			}

			//We must have an array identifier.
			*tokenToReturn = ARRAY_IDENTIFIER_TOKEN;
			return true;


		}

		*tokenToReturn = UNRECOGNISED_TOKEN;
		return false;
	}


	void SMTLIBOutputLexer::setInput(std::istream& i)
	{
		input = &i;
		lastTokenContents="";


	}

	std::istream& SMTLIBOutputLexer::getInput()
	{
		return *input;
	}


	const std::string& SMTLIBOutputLexer::getLastTokenContents()
	{
		return lastTokenContents;
	}

	bool SMTLIBOutputLexer::walkPastWhiteSpace()
	{
		//skip whitespace and newlines
		while(isspace(lastChar))
		{
			lastChar = input->get();

			if(input->eof())
			{
				//hit end of file
				*tokenToReturn = END_OF_FILE_TOKEN;
				return false;//User's expect this return value if hit end of file.
			}
		}


		return true;//didn't hit end of file
	}

bool SMTLIBOutputLexer::getLastNumericValue(unsigned long int& value)
{
	int base=0;

	switch(lastNumericToken)
	{
		case NUMERAL_BASE10_TOKEN: base=10; break;
		case NUMERAL_BASE16_TOKEN: base=16; break;
		case NUMERAL_BASE2_TOKEN:  base=2; break;
		default:
			return false;
	}

	errno=0;
	value=strtol(lastNumericTokenValue.c_str(),NULL,base);

	if(errno!=0)
		return false; //something went wrong
	else
		return true;

}

	bool SMTLIBOutputLexer::isIdentifier(char c)
	{
		return (isalnum(c) || c == '_' || c == '-' || c == '.');
	}

}




