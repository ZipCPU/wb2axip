--------------------------------------------------------------------------------
--
-- Filename: 	axlite_wrapper.vhd
--
-- Project:	Pipelined Wishbone to AXI converter
--
-- Purpose:	When wrapped with this wrapper, the axlite2wbsp.v core was
--		verified to work in FPGA silicon via Vivado.
--
--	Thank you Ambroz for donating this code!
--
-- Creator:	Ambroz Bizjak
--
--------------------------------------------------------------------------------
--
-- Copyright (C) 2019, Gisselquist Technology, LLC
--
-- This program is free software (firmware): you can redistribute it and/or
-- modify it under the terms of  the GNU General Public License as published
-- by the Free Software Foundation, either version 3 of the License, or (at
-- your option) any later version.
--
-- This program is distributed in the hope that it will be useful, but WITHOUT
-- ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
-- FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
-- for more details.
--
-- You should have received a copy of the GNU General Public License along
-- with this program.  (It's in the $(ROOT)/doc directory, run make with no
-- target there if the PDF file isn't present.)  If not, see
-- <http://www.gnu.org/licenses/> for a copy.
--
-- License:	GPL, v3, as defined and found on www.gnu.org,
--		http://www.gnu.org/licenses/gpl.html
--
--
--------------------------------------------------------------------------------
--
--
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
 
entity axlite2wbsp_wrapper is
    generic (
        C_AXI_ADDR_WIDTH : integer := 28;
        LGFIFO : integer := 4;
        F_MAXSTALL : integer := 3;
        F_MAXDELAY : integer := 3;
       
        --- Must not be changed.
        C_AXI_DATA_WIDTH : integer := 32
    );
    port (
        s_axi_aclk : in std_logic;        
        s_axi_aresetn : in std_logic;
       
        s_axi_awready : out std_logic;
        s_axi_awaddr : in std_logic_vector(C_AXI_ADDR_WIDTH-1 downto 0);
        s_axi_awcache : in std_logic_vector(3 downto 0);
        s_axi_awprot : in std_logic_vector(2 downto 0);
        s_axi_awvalid : in std_logic;
        s_axi_wready : out std_logic;
        s_axi_wdata : in std_logic_vector(C_AXI_DATA_WIDTH-1 downto 0);
        s_axi_wstrb : in std_logic_vector(C_AXI_DATA_WIDTH/8-1 downto 0);
        s_axi_wvalid : in std_logic;
        s_axi_bresp : out std_logic_vector(1 downto 0);
        s_axi_bvalid : out std_logic;
        s_axi_bready : in std_logic;
        s_axi_arready : out std_logic;
        s_axi_araddr : in std_logic_vector(C_AXI_ADDR_WIDTH-1 downto 0);
        s_axi_arcache : in std_logic_vector(3 downto 0);
        s_axi_arprot : in std_logic_vector(2 downto 0);
        s_axi_arvalid : in std_logic;
        s_axi_rresp : out std_logic_vector(1 downto 0);
        s_axi_rvalid : out std_logic;
        s_axi_rdata : out std_logic_vector(C_AXI_DATA_WIDTH-1 downto 0);
        s_axi_rready : in std_logic;
       
        m_wb_reset : out std_logic;
        m_wb_cyc : out std_logic;
        m_wb_stb : out std_logic;
        m_wb_we : out std_logic;
        m_wb_adr : out std_logic_vector(C_AXI_ADDR_WIDTH-2-1 downto 0);
        m_wb_dat_w : out std_logic_vector(C_AXI_DATA_WIDTH-1 downto 0);
        m_wb_sel : out std_logic_vector(C_AXI_DATA_WIDTH/8-1 downto 0);
        m_wb_ack : in std_logic;
        m_wb_stall : in std_logic;
        m_wb_dat_r : in std_logic_vector(C_AXI_DATA_WIDTH-1 downto 0);
        m_wb_err : in std_logic
    );
end axlite2wbsp_wrapper;
 
architecture Behavioral of axlite2wbsp_wrapper is
 
begin
    axlite2wbsp : entity work.axlite2wbsp
        generic map (
            C_AXI_ADDR_WIDTH => C_AXI_ADDR_WIDTH,
            LGFIFO => LGFIFO,
            F_MAXSTALL => F_MAXSTALL,
            F_MAXDELAY => F_MAXDELAY
        )
        port map (
            i_clk => s_axi_aclk,
            i_axi_reset_n => s_axi_aresetn,
            o_axi_awready => s_axi_awready,
            i_axi_awaddr => s_axi_awaddr,
            i_axi_awcache => s_axi_awcache,
            i_axi_awprot => s_axi_awprot,
            i_axi_awvalid => s_axi_awvalid,
            o_axi_wready => s_axi_wready,
            i_axi_wdata => s_axi_wdata,
            i_axi_wstrb => s_axi_wstrb,
            i_axi_wvalid => s_axi_wvalid,
            o_axi_bresp => s_axi_bresp,
            o_axi_bvalid => s_axi_bvalid,
            i_axi_bready => s_axi_bready,
            o_axi_arready => s_axi_arready,
            i_axi_araddr => s_axi_araddr,
            i_axi_arcache => s_axi_arcache,
            i_axi_arprot => s_axi_arprot,
            i_axi_arvalid => s_axi_arvalid,
            o_axi_rresp => s_axi_rresp,
            o_axi_rvalid => s_axi_rvalid,
            o_axi_rdata => s_axi_rdata,
            i_axi_rready => s_axi_rready,
            o_reset => m_wb_reset,
            o_wb_cyc => m_wb_cyc,
            o_wb_stb => m_wb_stb,
            o_wb_we => m_wb_we,
            o_wb_addr => m_wb_adr,
            o_wb_data => m_wb_dat_w,
            o_wb_sel => m_wb_sel,
            i_wb_ack => m_wb_ack,
            i_wb_stall => m_wb_stall,
            i_wb_data => m_wb_dat_r,
            i_wb_err => m_wb_err
        );
 
end Behavioral;
