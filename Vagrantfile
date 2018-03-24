# -*- mode: ruby -*-

Vagrant.configure(2) do |config|
  config.vm.box = 'ubuntu/xenial32'

  config.vm.provider 'virtualbox' do |vb|
    vb.name = 'CVC4'
    vb.memory = '8192'
    vb.cpus = 6
  end

  # config.vm.provision :shell, inline: 'su ubuntu /vagrant/provision.sh'
end
