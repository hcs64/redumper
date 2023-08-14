module;
#include <cstdint>

export module readers.form1_reader;

import cd.cdrom;
import readers.block_reader;



namespace gpsxre
{

export class Form1Reader : public BlockReader<uint32_t>
{
public:
	uint32_t blockSize() const override
	{
		return FORM1_DATA_SIZE;
	}
};

}
