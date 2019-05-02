pragma solidity ^0.5.0;

contract MillerRabin
{
    function modexp_rsa2048(uint256[8] memory b, uint256 e)
        public view returns(uint256[8] memory result)
    {
        bool success;
        assembly {
            let freemem := mload(0x40)

            // Length of base, exponent and modulus
            mstore(freemem, 0x100)              // base     (2048)
            mstore(add(freemem,0x20), 0x20)     // exponent (256)
            mstore(add(freemem,0x40), 0x100)    // modulus  (2048)

            // 2048bit base
            success := staticcall(sub(gas, 2000), 4, b, 0x100, add(freemem,0x60), 0x100)
            
            // 256bit exponent
            mstore(add(freemem,0x160), e)
            
            // Hard-coded RSA-2048 modulus
            mstore(add(freemem,0x180), 0xc7970ceedcc3b0754490201a7aa613cd73911081c790f5f1a8726f463550bb5b)
            mstore(add(freemem,0x1A0), 0x7ff0db8e1ea1189ec72f93d1650011bd721aeeacc2acde32a04107f0648c2813)
            mstore(add(freemem,0x1C0), 0xa31f5b0b7765ff8b44b4b6ffc93384b646eb09c7cf5e8592d40ea33c80039f35)
            mstore(add(freemem,0x1E0), 0xb4f14a04b51f7bfd781be4d1673164ba8eb991c2c4d730bbbe35f592bdef524a)
            mstore(add(freemem,0x200), 0xf7e8daefd26c66fc02c479af89d64d373f442709439de66ceb955f3ea37d5159)
            mstore(add(freemem,0x220), 0xf6135809f85334b5cb1813addc80cd05609f10ac6a95ad65872c909525bdad32)
            mstore(add(freemem,0x240), 0xbc729592642920f24c61dc5b3c3b7923e56b16a4d9d373d8721f24a3fc0f1b31)
            mstore(add(freemem,0x260), 0x31f55615172866bccc30f95054c824e733a5eb6817f7bc16399d48c6361cc7e5)

            success := staticcall(sub(gas, 2000), 0x0000000000000000000000000000000000000005, freemem, 0x280, result, 0x100)
        }
        require( success );
    }

    function modexp(uint256 b, uint256 e, uint256 m)
        public view returns(uint256 result)
    {
        bool success;
        assembly {
            let freemem := mload(0x40)
            mstore(freemem, 0x20)
            mstore(add(freemem,0x20), 0x20)
            mstore(add(freemem,0x40), 0x20)
            mstore(add(freemem,0x60), b)
            mstore(add(freemem,0x80), e)
            mstore(add(freemem,0xA0), m)
            success := staticcall(sub(gas, 2000), 5, freemem, 0xC0, freemem, 0x20)
            result := mload(freemem)
        }
        require(success);
    }

    function IsPrime(uint256 n, uint32 k, uint256 entropy)
        public view returns (bool)
    {
        if(n == 2)
            return true;
        
        if( n < 2 || n % 2 == 0 )
            return false;
        
        uint256 d = n - 1;
        uint256 s = 0;
        
        while( d % 2 == 0 ) {
            d = d / 2;
            s += 1;
        }
        
        while( k-- != 0 ) {
            // XXX: This is supposed to replace `rand(2, n-1)` but has small probabilitiy of incorrect value
            entropy = uint256(keccak256(abi.encodePacked(entropy, n))) % n;

            uint256 x = modexp(entropy, d, n);
            if (x == 1 || x == n-1)
                continue;
            
            bool ok = false;
                
            for( uint j = 1; j < s; j++ ) {
                x = mulmod(x, x, n);
                if( x == 1 )
                    return false;
                if(x == n-1) {
                    ok = true;
                    break;
                }
            }
            if ( false == ok ) {
                return false;
            }
        }
        return true;
    }
}